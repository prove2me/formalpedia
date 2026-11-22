-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch247_Segment000
-- name    : Polychromatic418967fa_Branch247_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:39:55.820422+00:00
-- url     : https://prove2.me/theorems/09f06aea-43b7-40ac-b2a2-493c8e30a3b5
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

def Polychromatic418967fa.branch_247_segment_000 : allB 123 247 :=
  allB_succ 122 247 (allA_of_3_1 122 122 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 121 247
  (allA_succ_of_accept 120 121 247 (Polychromatic418967fa.accept_16_8_9_7_1_768 120 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 247 (accept_3_3 119 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 247
  (Polychromatic418967fa.accept_22_7_11_5_1_13461 117 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 121 247 (accept_3_3 116 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 121 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 115 121 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27
  114 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 247 (accept_3_3
  113 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 247
  (Polychromatic418967fa.accept_22_2_11_5_1_11828 112 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 121 247 (Polychromatic418967fa.accept_15_6_1_7_1_4079 111 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 121 247 (accept_3_3 110 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 121 247 (Polychromatic418967fa.accept_16_13_9_7_1_4532 109
  121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 121 247
  (Polychromatic418967fa.accept_20_8_1_7_1_14906 108 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 121 247 (accept_3_3 107 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 247 (Polychromatic418967fa.accept_22_17_11_5_1_14910 105
  121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 121 247 (accept_3_3 104
  121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 121 247
  (Polychromatic418967fa.accept_22_15_11_5_1_13490 103 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 247 (accept_3_3 101 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 100
  121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 247
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 99 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 247 (accept_3_3 98 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 247 (Polychromatic418967fa.accept_22_9_11_5_1_7061 97 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 247 (Polychromatic418967fa.accept_10_6_1_7_1_342 96 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 247 (accept_3_3 95 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 121 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 247
  (Polychromatic418967fa.accept_16_13_9_7_1_4532 93 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 247 (accept_3_3 92 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 247 (Polychromatic418967fa.accept_20_11_1_7_1_9233 91 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 121 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 247 (accept_3_3 89 121 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 247 (Polychromatic418967fa.accept_16_8_9_7_1_768 88 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 247
  (Polychromatic418967fa.accept_25_12_21_22_1_14909 87 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 121 247 (accept_3_3 86 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 121 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 85 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 121 247 (Polychromatic418967fa.accept_10_4_1_7_1_371 84 121
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 247 (accept_3_3 83 121
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 121 247 (Polychromatic418967fa.accept_15_6_1_7_1_4079 81 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 121 247 (accept_3_3 80 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 121 247 (Polychromatic418967fa.accept_17_11_2_9_1_6358 79 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 121 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 121 247 (accept_3_3 77 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 121 247 (Polychromatic418967fa.accept_10_6_1_7_1_342 76 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 121 247 (Polychromatic418967fa.accept_17_7_2_9_1_6396 75 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 121 247 (accept_3_3 74 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 121 247 (Polychromatic418967fa.accept_22_7_11_5_1_13461 73 121
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 121 247
  (Polychromatic418967fa.accept_16_8_9_7_1_768 72 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 121 247 (accept_3_3 71 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 121 247 (Polychromatic418967fa.accept_15_9_1_7_1_1350 69 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 121 247 (accept_3_3 68 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 121 247 (Polychromatic418967fa.accept_16_3_9_7_1_6842 67 121
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 121 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 121 247 (accept_3_3 65 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 121 247 (Polychromatic418967fa.accept_10_4_1_7_1_371 64 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 121 247 (Polychromatic418967fa.accept_27_9_13_4_1_7170 63 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 247 (accept_3_3 62 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 247 (Polychromatic418967fa.accept_16_13_9_7_1_4532 61 121
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 247
  (Polychromatic418967fa.accept_22_16_11_5_1_11827 60 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 121 247 (accept_3_3 59 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 247 (Polychromatic418967fa.accept_22_13_11_5_1_1252 57 121
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 247 (accept_3_3 56 121
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 121 247
  (Polychromatic418967fa.accept_15_10_1_7_1_5207 55 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 247 (accept_3_3 53 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 121 247 (Polychromatic418967fa.accept_27_25_13_4_1_14908 52 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 247
  (Polychromatic418967fa.accept_15_6_1_7_1_4079 51 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 247 (accept_3_3 50 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 247 (Polychromatic418967fa.accept_25_24_21_22_1_14907 49 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 247 (Polychromatic418967fa.accept_20_8_1_7_1_14906 48 121 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 247 (accept_3_3 47 121 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 247
  (Polychromatic418967fa.accept_16_13_9_7_1_4532 45 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 247 (accept_3_3 44 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 247 (Polychromatic418967fa.accept_24_19_1_7_1_9846 43 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 247 (accept_3_3 41 121 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 40 121 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 247
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 39 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 247 (accept_3_3 38 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 247 (Polychromatic418967fa.accept_22_15_11_5_1_13490 37 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 247 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 247 (accept_3_3 35 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 247
  (Polychromatic418967fa.accept_23_10_6_17_1_14905 33 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 121 247 (accept_3_3 32 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 121 247 (Polychromatic418967fa.accept_20_11_1_7_1_9233 31 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 247 (accept_3_3 29 121 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 247
  (Polychromatic418967fa.accept_17_11_2_9_1_6358 28 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 121 247 (Polychromatic418967fa.accept_23_4_6_17_1_6655 27 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 247 (accept_3_3 26 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 121 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 25 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 247
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 247 (accept_3_3 23 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 247 (Polychromatic418967fa.accept_15_6_1_7_1_4079 21 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 247 (accept_3_3 20 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 247 (Polychromatic418967fa.accept_16_3_9_7_1_6842 19 121
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 247 (accept_3_3 17 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 247 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 247 (Polychromatic418967fa.accept_20_15_1_7_1_9235 15 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 247 (accept_3_3 14 121 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 247 (Polychromatic418967fa.accept_16_13_9_7_1_4532 13 121
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 247
  (Polychromatic418967fa.accept_23_12_6_17_1_14904 12 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 121 247 (accept_3_3 11 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 121 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 247 (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 121 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 247 (accept_3_3 8 121 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 247 (Polychromatic418967fa.accept_17_7_2_9_1_6396
  7 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 247 (accept_3_3 5 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 247 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 121 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 247 (Polychromatic418967fa.accept_16_3_9_7_1_6842 3 121 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 247 (accept_3_3 2 121 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 247 (Polychromatic418967fa.accept_25_1_21_22_1_14903 1 121 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 247 (allA_succ_of_accept 119 120 247 (accept_3_3 119 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 120 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 118 120 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 120 247 (Polychromatic418967fa.accept_17_15_1_9_1_10058 117
  120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 247 (accept_3_3 116
  120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 120 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 115 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 120 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 114 120 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 120 247 (accept_3_3 113 120 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 120 247 (Polychromatic418967fa.accept_17_10_1_9_1_11372 112 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 111 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 120 247 (accept_3_3 110 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 120 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 109 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 120 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 108 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 247 (accept_3_3 107 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 106 120
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 120 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 105 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 120 247 (accept_3_3 104 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 120 247 (Polychromatic418967fa.accept_11_4_10_5_1_1202 103 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 120 247 (Polychromatic418967fa.accept_21_18_15_16_1_2917 102 120 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 120 247 (accept_3_3 101 120 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 247 (Polychromatic418967fa.accept_9_1_3_4_1_47
  100 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 247
  (Polychromatic418967fa.accept_14_1_8_9_1_1312 99 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 120 247 (accept_3_3 98 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 120 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 97 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 120 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 96 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 120 247 (accept_3_3 95 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 94 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 247
  (Polychromatic418967fa.accept_17_8_1_9_1_7738 93 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 120 247 (accept_3_3 92 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 120 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 120 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 120 247 (accept_3_3 89 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 87 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 120 247 (accept_3_3 86 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 120 247 (Polychromatic418967fa.accept_14_1_8_9_1_1312 85 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 120 247 (Polychromatic418967fa.accept_16_4_8_7_1_3396 84 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 120 247 (accept_3_3 83 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 120 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 247
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 81 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 120 247 (accept_3_3 80 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 120 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 120 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 247 (accept_3_3 77 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 247
  (Polychromatic418967fa.accept_18_3_12_13_1_3307 75 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 120 247 (accept_3_3 74 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 120 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 73 120 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 120 247 (Polychromatic418967fa.accept_11_6_10_5_1_341 72 120
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 120 247 (accept_3_3 71 120
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 247
  (Polychromatic418967fa.accept_9_7_3_4_1_218 70 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 120 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 120 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 247 (accept_3_3 68 120 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 120 247 (Polychromatic418967fa.accept_22_1_10_5_1_14902 67 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 120 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 66 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 120 247 (accept_3_3 65 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 120 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 120 247 (Polychromatic418967fa.accept_16_15_8_7_1_3407 63 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 247 (accept_3_3 62 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 120 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 120 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 120 247 (accept_3_3 59 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 120 247 (Polychromatic418967fa.accept_23_12_5_17_1_14901 58 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 247 (Polychromatic418967fa.accept_14_1_8_9_1_1312 57 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 247 (accept_3_3 56 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 120 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 120 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 120 247
  (Polychromatic418967fa.accept_17_3_1_9_1_9012 54 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 120 247 (accept_3_3 53 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 120 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 120 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 247 (accept_3_3 50 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 247 (Polychromatic418967fa.accept_16_1_8_7_1_3377 49 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 120 247 (accept_3_3 47 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 120 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 120 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 247 (accept_3_3 44 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 120 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 120 247 (accept_3_3 41 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 120 247 (Polychromatic418967fa.accept_25_15_20_22_1_14900 40 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 247 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 247 (accept_3_3 38 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 120 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 247
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 36 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 120 247 (accept_3_3 35 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 120 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 120 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 247 (accept_3_3 32 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 247
  (Polychromatic418967fa.accept_21_9_15_16_1_4328 30 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 120 247 (accept_3_3 29 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 120 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 120 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 120 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 247 (accept_3_3 26 120 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 247 (Polychromatic418967fa.accept_9_7_3_4_1_218
  25 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 120 247 (accept_3_3 23 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 120 247 (Polychromatic418967fa.accept_21_1_15_16_1_5891 22 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 120 247 (Polychromatic418967fa.accept_18_3_12_13_1_3307 21 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 247 (accept_3_3 20 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 120 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 247
  (Polychromatic418967fa.accept_21_18_15_16_1_2917 18 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 247 (accept_3_3 17 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 120 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 120 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 247 (accept_3_3 14 120 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 247 (Polychromatic418967fa.accept_7_6_1_2_1_230
  13 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 247
  (Polychromatic418967fa.accept_16_12_8_7_1_4530 12 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 120 247 (accept_3_3 11 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 120 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 120 247 (Polychromatic418967fa.accept_16_9_8_7_1_4529 9 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 247 (accept_3_3 8 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 120 247 (accept_3_3 5 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  120 247 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 120 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 120 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 247 (accept_3_3 2 120 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 120 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 247 (allA_of_3_1 119 119 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 118 247
  (allA_succ_of_accept 117 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 118 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 118 247 (accept_3_3 116 118 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 118 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 115 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 118 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 114 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 118 247 (accept_3_3 113 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 118 247 (Polychromatic418967fa.accept_11_2_8_5_1_1219 112 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 118 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 118 247 (accept_3_3 110 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 109 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 118 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 108 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 118 247 (accept_3_3 107 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 118 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 106 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 118 247 (accept_3_3 104 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 118 247 (Polychromatic418967fa.accept_21_19_13_16_1_7317 103 118 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 118 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 102 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 118 247 (accept_3_3 101 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 118 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 100 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 118 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 118 247 (accept_3_3 98 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 118 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 96 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 118 247 (accept_3_3 95 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 118 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 94 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 118 247 (accept_3_3 92 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 118 247 (Polychromatic418967fa.accept_11_3_8_5_1_336 91 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 118 247
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 90 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 118 247 (accept_3_3 89 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 118 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 88 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 118 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 118 247 (accept_3_3 86 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 118 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 118 247 (accept_3_3 83 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 118 247 (Polychromatic418967fa.accept_20_2_18_7_1_3394 82 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 118 247 (accept_3_3 80 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 118 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 118 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 78 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 118 247 (accept_3_3 77 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 118 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 118 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 247 (accept_3_3 74 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 247
  (Polychromatic418967fa.accept_21_9_13_16_1_2914 72 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 118 247 (accept_3_3 71 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 118 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 118 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 118 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 247 (accept_3_3 68 118 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 247 (Polychromatic418967fa.accept_7_4_6_2_1_451
  67 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 247 (accept_3_3 65 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 247 (accept_3_3 62 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 247 (accept_3_3 59 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 247 (Polychromatic418967fa.accept_11_3_8_5_1_336 58 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 247 (accept_3_3 56 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 247 (Polychromatic418967fa.accept_10_5_8_7_1_2174 55 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 247
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 54 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 247 (accept_3_3 53 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 247 (accept_3_3 50 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 247 (accept_3_3 47 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 247 (accept_3_3 44 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 247 (accept_3_3 41 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 247 (accept_3_3 38 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 247 (accept_3_3 35 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 247 (accept_3_3 32 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 247 (accept_3_3 29 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 247 (accept_3_3 26 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 247 (accept_3_3 23 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 247 (accept_3_3 20 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 247 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 247 (accept_3_3 17 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 247 (accept_3_3 14 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 247 (accept_3_3 11 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 247 (accept_3_3 8 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 247 (accept_3_3 5 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 118 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 247 (accept_3_3 2 118 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 247 (allA_succ_of_accept 116 117 247 (accept_3_3 116 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 115 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 117
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 247 (accept_3_3 113 117
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 247
  (Polychromatic418967fa.accept_6_4_3_1_1_57 112 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 117 247 (Polychromatic418967fa.accept_12_3_9_7_1_472 111 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 247 (accept_3_3 110 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 117 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 109 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 108 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 117 247 (accept_3_3 107 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 117 247 (Polychromatic418967fa.accept_14_7_5_9_1_2911 105 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 117 247 13 8 9 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 117 247
  (Polychromatic418967fa.accept_17_1_15_9_1_1743 103 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 247 (accept_3_3 101 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 117
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 117 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 99 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 117 247 (accept_3_3 98 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 117 247 (Polychromatic418967fa.accept_11_9_7_5_1_749 97 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 117 247 (Polychromatic418967fa.accept_15_6_12_7_1_1360 96 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 247 (accept_3_3 95 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 117 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 247
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 93 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 117 247 (accept_3_3 92 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91
  117 247 13 7 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  90 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 247 (accept_3_3 89 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 117 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 247 (accept_3_3 86 117 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 247
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 85 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 117 247 (Polychromatic418967fa.accept_20_4_17_7_1_3393 84 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 247 (accept_3_3 83 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 117 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 117 247 (accept_3_3 80 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 117 247 (Polychromatic418967fa.accept_15_4_12_7_1_3115 79 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 117 247 13 6 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 117 247 (accept_3_3 77 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 247 (Polychromatic418967fa.accept_11_9_7_5_1_749 75 117
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 247 (accept_3_3 74 117
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 73 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 117 247 (Polychromatic418967fa.accept_20_12_17_7_1_4786 72 117 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 247 (accept_3_3 71 117 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 247
  (Polychromatic418967fa.accept_17_1_15_9_1_1743 69 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 117 247 (accept_3_3 68 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 117 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 117 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 117 247 13 5 9 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 117 247
  (Polychromatic418967fa.accept_6_4_3_1_1_57 64 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 117 247 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 247 (accept_3_3 62 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 117 247 (Polychromatic418967fa.accept_23_15_2_17_1_13353 61 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 117 247 (accept_3_3 59 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 117 247 (Polychromatic418967fa.accept_17_6_15_9_1_1791 57 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 247 (accept_3_3 56 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 247 (Polychromatic418967fa.accept_15_10_12_7_1_1358 55 117
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 117 247 (accept_3_3 53 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52
  117 247 13 4 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  51 117 247 (Polychromatic418967fa.accept_12_3_9_7_1_472 51 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 247 (accept_3_3 50 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 247 (Polychromatic418967fa.accept_14_7_5_9_1_2911 49 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 247 (Polychromatic418967fa.accept_15_3_12_7_1_1346 48 117
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 247 (accept_3_3 47 117
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 117 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 247 (accept_3_3 44 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 117 247 (Polychromatic418967fa.accept_16_11_5_7_1_2395 43 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 247 (accept_3_3 41 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 117 247 13 3 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 117 247 (accept_3_3 38 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 247 (Polychromatic418967fa.accept_24_13_21_7_1_4502 37 117 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 247
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 117 247 (accept_3_3 35 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 247 (Polychromatic418967fa.accept_15_3_12_7_1_1346 33 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 247 (accept_3_3 32 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 117 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 117 247 (accept_3_3 29 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 117 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 247 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 117 247 13 2 9 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 117 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 117 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 247 (accept_3_3 23 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 247 (Polychromatic418967fa.accept_14_7_5_9_1_2911
  21 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 247 (accept_3_3 20
  117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 247
  (Polychromatic418967fa.accept_15_4_12_7_1_3115 19 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 247 (accept_3_3 17 117 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 117 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 247 (Polychromatic418967fa.accept_12_3_9_7_1_472
  15 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 247 (accept_3_3 14
  117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 117 247 13 1 9 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 117 247
  (Polychromatic418967fa.accept_16_12_5_7_1_2360 12 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 247 (accept_3_3 11 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 247 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 117 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 247 (accept_3_3 8 117 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 247 (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 247 (accept_3_3 5 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 117 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 247 (accept_3_3 2 117 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 247 (Polychromatic418967fa.accept_17_1_15_9_1_1743 1 117 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 247 (allA_of_3_1 116 116 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 247
  (allA_succ_of_accept 114 115 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 114 115 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 247 (accept_3_3 113 115 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 115 247 (Polychromatic418967fa.accept_10_2_5_7_1_1124 112 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 111 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 115 247 (accept_3_3 110 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 115 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 109 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 115 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 108 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 115 247 (accept_3_3 107 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 115 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 106 115
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 115 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 105 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 115 247 (accept_3_3 104 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 115 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 103 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 115 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 102 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 115 247 (accept_3_3 101 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 115 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 100 115
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 115 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 99 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 115 247 (accept_3_3 98 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 115 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 97 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 115 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 115 247 (accept_3_3 95 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 115 247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 94 115 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 93 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 115 247 (accept_3_3 92 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 115 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 115 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 115 247 (accept_3_3 89 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 247 (Polychromatic418967fa.accept_10_8_5_7_1_358 88 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 87 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 247 (accept_3_3 86 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 115 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 85 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 115 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 247 (accept_3_3 83 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 82 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 247
  (Polychromatic418967fa.accept_20_1_15_7_1_3405 81 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 115 247 (accept_3_3 80 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 115 247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 79 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 115 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 247 (accept_3_3 77 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 115 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 76 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 115 247 (accept_3_3 74 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 115 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 115 247 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 247 (accept_3_3 71 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 115 247 (Polychromatic418967fa.accept_20_10_15_7_1_6312 70 115
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 115 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 247 (accept_3_3 68 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 247 (Polychromatic418967fa.accept_17_16_13_9_1_11391 67 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 247 (accept_3_3 65 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 115 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 115 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 247
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 115 247 (accept_3_3 62 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 115 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 115 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 247 (accept_3_3 59 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 247 (Polychromatic418967fa.accept_10_8_5_7_1_358 58 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 247 (accept_3_3 56 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 115 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 115 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 247 (accept_3_3 53 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 115 247 (accept_3_3 50 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 115 247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 49 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 247 (accept_3_3 47 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 247
  (Polychromatic418967fa.accept_20_5_15_7_1_7869 45 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 247 (accept_3_3 44 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 247 (accept_3_3 41 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 247 (accept_3_3 38 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 247 (accept_3_3 35 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 247 (accept_3_3 32 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 31 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 247 (accept_3_3 29 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 247 (accept_3_3 26 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 247 (Polychromatic418967fa.accept_16_9_3_7_1_6883 25 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 247 (accept_3_3 23 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 247 (accept_3_3 20 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 247 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 247 (accept_3_3 17 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 115
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 247 (accept_3_3 14 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 247 (accept_3_3 11 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 247
  (Polychromatic418967fa.accept_16_9_3_7_1_6883 9 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 247 (accept_3_3 8 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 247 (Polychromatic418967fa.accept_21_7_10_16_1_4338 7 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 247 (accept_3_3 5 115 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 115 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 247 (accept_3_3 2 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 115 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 247 (allA_succ_of_accept 113 114 247 (accept_3_3 113 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 114 247 (Polychromatic418967fa.accept_10_2_4_7_1_352 112 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 114 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 111 114
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 247 (accept_3_3 110 114
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 114 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 114 247 (Polychromatic418967fa.accept_16_12_2_7_1_6853 108 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 247 (accept_3_3 107 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 106 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 114 247 (accept_3_3 104 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 114 247 (Polychromatic418967fa.accept_10_3_4_7_1_353 103 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 114 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 102 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 247 (accept_3_3 101 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 100 114
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 247
  (Polychromatic418967fa.accept_17_14_12_9_1_2774 99 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 114 247 (accept_3_3 98 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 114 247 (Polychromatic418967fa.accept_21_12_9_16_1_11973 96
  114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 114 247 19 5 6 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 114 247
  (Polychromatic418967fa.accept_21_10_9_16_1_9073 94 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 247 (accept_3_3 92 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 114 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 114 247
  (Polychromatic418967fa.accept_17_5_12_9_1_10091 90 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 114 247 (accept_3_3 89 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 114 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 247 (Polychromatic418967fa.accept_11_10_4_5_1_359 87 114
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 247 (accept_3_3 86 114
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9
  85 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 114 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 114 247 (accept_3_3 83 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 114 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 247 (accept_3_3 80 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 114 247
  (Polychromatic418967fa.accept_21_15_9_16_1_7341 78 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 114 247 (accept_3_3 77 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 114 247 19 4 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 114 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 247 (accept_3_3 74 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 114 247 (Polychromatic418967fa.accept_10_2_4_7_1_352
  72 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 114 247 (accept_3_3 71
  114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 247
  (Polychromatic418967fa.accept_9_7_6_4_1_483 70 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 247 (accept_3_3 68 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 114 247 (Polychromatic418967fa.accept_14_11_2_9_1_5873 67 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 114 247 (accept_3_3 65 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 114 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 114 247 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 247 (accept_3_3 62 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 114 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 247
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 60 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 114 247 (accept_3_3 59 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 114 247 (Polychromatic418967fa.accept_15_13_9_7_1_2194 58 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 114 247 19 3 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 114 247 (accept_3_3 56 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 114 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 247 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 114
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 247 (accept_3_3 53 114
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 247
  (Polychromatic418967fa.accept_9_7_6_4_1_483 52 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 114 247 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 247 (accept_3_3 50 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 247 (Polychromatic418967fa.accept_9_3_6_4_1_210
  48 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 247 (accept_3_3 47
  114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 247
  (Polychromatic418967fa.accept_9_1_6_4_1_49 46 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 247 (accept_3_3 44 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 114 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 247 (Polychromatic418967fa.accept_10_2_4_7_1_352
  42 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 247 (accept_3_3 41
  114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 247
  (Polychromatic418967fa.accept_22_18_4_5_1_10433 40 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 114 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 247 19 2 6 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 114 247 (Polychromatic418967fa.accept_21_15_9_16_1_7341 36 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 247 (accept_3_3 35 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 114 247 (accept_3_3 32 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 114 247 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 114 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 247 (accept_3_3 29 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 247
  (Polychromatic418967fa.accept_16_11_2_7_1_3374 27 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 114 247 (accept_3_3 26 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 114 247 (Polychromatic418967fa.accept_21_3_9_16_1_10597 24 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 247 (accept_3_3 23 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 247 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 114
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 114 247 (accept_3_3 20 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19
  114 247 19 1 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  18 114 247 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 114 247 (accept_3_3 17 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 114 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 247 (Polychromatic418967fa.accept_21_15_9_16_1_7341 15 114
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 247 (accept_3_3 14 114
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9
  13 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 247 (accept_3_3 11 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 114 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 247 (accept_3_3 8 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 247
  (Polychromatic418967fa.accept_21_6_9_16_1_2939 6 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 247 (accept_3_3 5 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  114 247 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 114 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 247 (accept_3_3 2 114 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 247 (allA_of_3_1 113 113 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 247
  (allA_succ_of_accept 111 112 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 112 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 112 247 (accept_3_3 110 112 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 112 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 109 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 112 247
  (Polychromatic418967fa.accept_21_3_7_16_1_11967 108 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 112 247 (accept_3_3 107 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 112 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 106 112 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 112 247 (Polychromatic418967fa.accept_6_3_4_1_1_8
  105 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 112 247 (accept_3_3
  104 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 112 247
  (Polychromatic418967fa.accept_17_1_10_9_1_3884 103 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 112 247 (Polychromatic418967fa.accept_20_2_12_7_1_4799 102 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 112 247 (accept_3_3 101 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 112 247 (Polychromatic418967fa.accept_18_10_4_13_1_3296 100
  112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 112 247 (accept_3_3 98 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 112 247 (Polychromatic418967fa.accept_18_7_4_13_1_3315 97 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 112 247 (Polychromatic418967fa.accept_11_8_2_5_1_1769 96 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 112 247 (accept_3_3 95 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 112 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 94 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 112 247 (accept_3_3 92 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 112 247 (Polychromatic418967fa.accept_22_3_2_5_1_14899 91 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 112 247 (Polychromatic418967fa.accept_21_6_7_16_1_9035 90 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 112 247 (accept_3_3 89 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 112 247 (Polychromatic418967fa.accept_17_3_10_9_1_8970 88 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 112 247 (accept_3_3 86 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 112 247 (Polychromatic418967fa.accept_10_5_2_7_1_345 85 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 112 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 84 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 112 247 (accept_3_3 83 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 112 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 112 247 (accept_3_3 80 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 112 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 79 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 112 247 (Polychromatic418967fa.accept_22_12_2_5_1_14898 78 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 112 247 (accept_3_3 77 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 112 247 (Polychromatic418967fa.accept_21_13_7_16_1_7351 76 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 112 247 (accept_3_3 74 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 112 247 (Polychromatic418967fa.accept_21_10_7_16_1_9036 73 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 112 247 (Polychromatic418967fa.accept_21_9_7_16_1_5904 72 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 112 247 (accept_3_3 71 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 112 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 112 247 (accept_3_3 68 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 112 247 (Polychromatic418967fa.accept_17_16_10_9_1_11361 67 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 112 247 (Polychromatic418967fa.accept_20_6_12_7_1_12130 66 112 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 247 (accept_3_3 65 112 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 112 247 (Polychromatic418967fa.accept_10_4_2_7_1_373
  64 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 112 247 (accept_3_3 62 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 112 247 (Polychromatic418967fa.accept_18_7_4_13_1_3315 61 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 112 247 (Polychromatic418967fa.accept_23_14_20_17_1_4986 60 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 247 (accept_3_3 59 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 112 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 247 (accept_3_3 56 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 247 (Polychromatic418967fa.accept_10_5_2_7_1_345 55 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 247 (accept_3_3 53 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 247 (Polychromatic418967fa.accept_11_8_2_5_1_1769 52 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 247 (accept_3_3 50 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 247 (Polychromatic418967fa.accept_21_6_7_16_1_9035 48 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 247 (accept_3_3 47 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 247 (accept_3_3 44 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 247 (Polychromatic418967fa.accept_18_7_4_13_1_3315 43 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 247 (Polychromatic418967fa.accept_20_2_12_7_1_4799 42 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 247 (accept_3_3 41 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 247 (Polychromatic418967fa.accept_22_18_2_5_1_14819 40 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 247 (accept_3_3 38 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 247 (Polychromatic418967fa.accept_17_3_10_9_1_8970 37 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 247 (Polychromatic418967fa.accept_24_12_16_7_1_9876 36 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 247 (accept_3_3 35 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 247 (accept_3_3 32 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 247 (Polychromatic418967fa.accept_21_10_7_16_1_9036 31 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 247 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 247 (accept_3_3 29 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 247 (Polychromatic418967fa.accept_18_10_4_13_1_3296 28 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 247 (accept_3_3 26 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 247 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 247 (accept_3_3 23 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 247 (accept_3_3 20 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 247 (Polychromatic418967fa.accept_17_1_10_9_1_3884 18 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 247 (accept_3_3 17 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 247 (Polychromatic418967fa.accept_17_16_10_9_1_11361 16
  112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 247 (accept_3_3 14 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 247 (Polychromatic418967fa.accept_17_13_10_9_1_946 13 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 112 247 (Polychromatic418967fa.accept_21_12_7_16_1_9024 12 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 247 (accept_3_3 11 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 112
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 247 (accept_3_3 8 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 247 (Polychromatic418967fa.accept_18_7_4_13_1_3315 7 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 247 (Polychromatic418967fa.accept_20_6_12_7_1_12130 6 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 247 (accept_3_3 5 112 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 112 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 247 (accept_3_3 2 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 247 (Polychromatic418967fa.accept_17_1_10_9_1_3884 1 112 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 247 (allA_succ_of_accept 110 111 247 (accept_3_3 110 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 109 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 108 111
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 247 (accept_3_3 107 111
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 247
  (Polychromatic418967fa.accept_6_4_3_1_1_57 106 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 111 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 105 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 247 (accept_3_3 104 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 111 247 (Polychromatic418967fa.accept_15_13_6_7_1_1369 103 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 102 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 111 247 (accept_3_3 101 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 111 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 99 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 247 (accept_3_3 98 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 97 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 96 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 111 247 (accept_3_3 95 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 111 247 (Polychromatic418967fa.accept_12_9_3_7_1_924 93 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 247 (accept_3_3 92 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 111 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 247
  (Polychromatic418967fa.accept_20_10_11_7_1_4796 90 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 111 247 (accept_3_3 89 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 111 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 111 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 247 (accept_3_3 86 111 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 85
  111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 247
  (Polychromatic418967fa.accept_10_4_1_7_1_371 84 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 247 (accept_3_3 83 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 111 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 247 (accept_3_3 80 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 78 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 247 (accept_3_3 77 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 247 (Polychromatic418967fa.accept_16_11_15_7_1_5654 75 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 247 (accept_3_3 74 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 111 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 247
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 111 247 (accept_3_3 71 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 247 (accept_3_3 68 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 247 (accept_3_3 65 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 247 (Polychromatic418967fa.accept_18_9_3_13_1_5905 63 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 247 (accept_3_3 62 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 111 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 247 (accept_3_3 59 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 247 (accept_3_3 56 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 247
  (Polychromatic418967fa.accept_10_4_1_7_1_371 54 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 247 (accept_3_3 53 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 247 (accept_3_3 50 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 247 (Polychromatic418967fa.accept_21_7_6_16_1_5834 49 111 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 247
  (Polychromatic418967fa.accept_18_12_3_13_1_4494 48 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 111 247 (accept_3_3 47 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 111 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 247 (accept_3_3 44 111 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 43
  111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 247 (accept_3_3 41 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 247 (accept_3_3 38 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 247 (accept_3_3 35 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 247 (accept_3_3 32 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 111 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 247
  (Polychromatic418967fa.accept_16_14_15_7_1_5655 30 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 247 (accept_3_3 29 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 247 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 111
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 247 (accept_3_3 26 111
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 111 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 247 (accept_3_3 23 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 247 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 247 (accept_3_3 20
  111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 247
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 111 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 247 (accept_3_3 17 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 247 (accept_3_3 14
  111 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 247
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 111 247 (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 247 (accept_3_3 11 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 247 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 247 (accept_3_3 8 111
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 247
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 111 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 247 (accept_3_3 5 111 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 111 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 3
  111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 247 (accept_3_3 2 111
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 247 (Polychromatic418967fa.accept_7_1_6_2_1_18
  1 111 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 247 (allA_of_3_1 110 110 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 247
  (allA_succ_of_accept 108 109 247 (Polychromatic418967fa.accept_10_8_9_7_1_1118 108 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 247 (accept_3_3 107 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 105 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 247 (accept_3_3 104 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 103 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 247 (accept_3_3 101 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 247 (Polychromatic418967fa.accept_14_2_11_9_1_2925 100
  109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 247
  (Polychromatic418967fa.accept_26_21_5_13_1_7414 99 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 109 247 (accept_3_3 98 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 109 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 97 109 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 109 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 96 109 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 247 (accept_3_3 95 109 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 94
  109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 93 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 247 (accept_3_3 92 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 247 (Polychromatic418967fa.accept_21_7_4_16_1_5888 91 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 247 (accept_3_3 89 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 87 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 247 (accept_3_3 86 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 247 (Polychromatic418967fa.accept_15_10_4_7_1_3127 85 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 247 (accept_3_3 83 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 247
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 81 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 247 (accept_3_3 80 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 247 (accept_3_3 77 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 76 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 247 (accept_3_3 74 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 247 (Polychromatic418967fa.accept_16_9_13_7_1_1509 73 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 247 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 247 (accept_3_3 71 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 109 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 247 (accept_3_3 68 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 247 (Polychromatic418967fa.accept_22_1_21_5_1_10380 67 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 247 (accept_3_3 65 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 247 (Polychromatic418967fa.accept_18_10_1_13_1_2192 64 109 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 247
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 63 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 247 (accept_3_3 62 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 247 (accept_3_3 59 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 247 (accept_3_3 56 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 247 (accept_3_3 53 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 51 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 247 (accept_3_3 50 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 247 (Polychromatic418967fa.accept_17_15_7_9_1_1809 49 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 247 (accept_3_3 47 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 247
  (Polychromatic418967fa.accept_20_5_9_7_1_10766 45 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 247 (accept_3_3 44 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 247 (accept_3_3 41 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 247 (accept_3_3 38 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 247 (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 247 (Polychromatic418967fa.accept_16_4_13_7_1_4522 36 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 247 (accept_3_3 35 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 247 (accept_3_3 32 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 247 (Polychromatic418967fa.accept_21_10_4_16_1_9079 31 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 247 (accept_3_3 29 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 247 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 247 (accept_3_3 26 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 247 (accept_3_3 23 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 247 (accept_3_3 20 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 247 (accept_3_3 17 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 247 (accept_3_3 14 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 247 (accept_3_3 11 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 247
  (Polychromatic418967fa.accept_16_9_13_7_1_1509 9 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 247 (accept_3_3 8 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 247 (accept_3_3 5 109 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 247 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 109 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 247 (accept_3_3 2 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 247 (Polychromatic418967fa.accept_22_1_21_5_1_10380 1 109 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 247 (allA_succ_of_accept 107 108 247 (accept_3_3 107 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 108 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 106 108 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 247 (Polychromatic418967fa.accept_10_5_8_7_1_2174 105 108
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 247 (accept_3_3 104 108
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 108 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 103 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 108 247 (Polychromatic418967fa.accept_15_12_3_7_1_4123 102 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 247 (accept_3_3 101 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 247 (Polychromatic418967fa.accept_15_10_3_7_1_715 100 108 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 99 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 108 247 (accept_3_3 98 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 108 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 97 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 108 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 108 247 (accept_3_3 95 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 247 (Polychromatic418967fa.accept_15_4_3_7_1_713 94 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 247
  (Polychromatic418967fa.accept_17_8_6_9_1_7768 93 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 108 247 (accept_3_3 92 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 108 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 91 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 108 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 108 247 (accept_3_3 89 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 247 (Polychromatic418967fa.accept_16_8_12_7_1_2399 88 108 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 247
  (Polychromatic418967fa.accept_15_12_3_7_1_4123 87 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 108 247 (accept_3_3 86 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 108 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 85 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 108 247 (Polychromatic418967fa.accept_11_7_9_5_1_338 84 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 247 (accept_3_3 83 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 82 108 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 247
  (Polychromatic418967fa.accept_20_1_8_7_1_7856 81 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 108 247 (accept_3_3 80 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 108 247 (Polychromatic418967fa.accept_10_9_8_7_1_714 79 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 108 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 247 (accept_3_3 77 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 76 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 108 247 (accept_3_3 74 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 108 247 (Polychromatic418967fa.accept_11_7_9_5_1_338 73 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 108 247 (Polychromatic418967fa.accept_15_12_3_7_1_4123 72 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 247 (accept_3_3 71 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 247 (Polychromatic418967fa.accept_15_10_3_7_1_715 70 108
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 108 247 (accept_3_3 68 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 108 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 108 247 (Polychromatic418967fa.accept_16_2_12_7_1_3410 66 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 108 247 (accept_3_3 65 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 108 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 247
  (Polychromatic418967fa.accept_25_13_8_22_1_14897 63 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 108 247 (accept_3_3 62 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 108 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 108 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 108 247 (Polychromatic418967fa.accept_21_18_3_16_1_5833 60 108
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 108 247 (accept_3_3 59 108
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 247
  (Polychromatic418967fa.accept_33_25_9_16_1_14896 58 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 108 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 247 (accept_3_3 56 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 54 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 108 247 (accept_3_3 53 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 108 247 (Polychromatic418967fa.accept_16_4_12_7_1_4475 52 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 108 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 247 (accept_3_3 50 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 247 (Polychromatic418967fa.accept_10_9_8_7_1_714 49 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 108 247 (accept_3_3 47 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 108 247 (Polychromatic418967fa.accept_25_21_8_22_1_14895 46 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 247 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 247 (accept_3_3 44 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 108 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 247
  (Polychromatic418967fa.accept_15_12_3_7_1_4123 42 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 108 247 (accept_3_3 41 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 108 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 108 247 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 247 (accept_3_3 38 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 247 (Polychromatic418967fa.accept_16_5_12_7_1_3411 37 108
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 108 247 (accept_3_3 35 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 108 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 108 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 247 (accept_3_3 32 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 247 (Polychromatic418967fa.accept_21_10_3_16_1_5909 31 108 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 247
  (Polychromatic418967fa.accept_20_10_8_7_1_7834 30 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 108 247 (accept_3_3 29 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 108 247 (Polychromatic418967fa.accept_21_7_3_16_1_7337 28 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 108 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 247 (accept_3_3 26 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 247 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 247
  (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 108 247 (accept_3_3 23 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 108 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 108 247 (Polychromatic418967fa.accept_16_5_12_7_1_3411 21 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 247 (accept_3_3 20 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 108 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 247
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 108 247 (accept_3_3 17 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 108 247 (Polychromatic418967fa.accept_17_16_6_9_1_7769 16 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 108 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 247 (accept_3_3 14 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 108 247 (accept_3_3 11 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 108 247 (Polychromatic418967fa.accept_15_10_3_7_1_715 10 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 108 247 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 247 (accept_3_3 8 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 247 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 108 247 (accept_3_3 5 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  108 247 (Polychromatic418967fa.accept_15_4_3_7_1_713 4 108 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 108 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 247 (accept_3_3 2 108 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 108 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 247 (allA_of_3_1 107 107 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 247
  (allA_succ_of_accept 105 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 106 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 247 (accept_3_3 104 106 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 106 247 (Polychromatic418967fa.accept_10_3_6_7_1_2188 103 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 102 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 106 247 (accept_3_3 101 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 106 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 100 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 106 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 247 (accept_3_3 98 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 96 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 247 (accept_3_3 95 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 94 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 247 (accept_3_3 92 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 90 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 106 247 (accept_3_3 89 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 106 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 106 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 247 (accept_3_3 86 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 247 (accept_3_3 83 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 247 (accept_3_3 80 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 247 (Polychromatic418967fa.accept_20_19_6_7_1_9289 79 106 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 247 (accept_3_3 77 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 247 (accept_3_3 74 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 247
  (Polychromatic418967fa.accept_20_12_6_7_1_7875 72 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 247 (accept_3_3 71 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 70 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 247 (accept_3_3 68 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 247 (Polychromatic418967fa.accept_16_3_10_7_1_4518 67 106 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 66 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 247 (accept_3_3 65 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 247 (accept_3_3 62 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 247 (accept_3_3 59 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 247 (Polychromatic418967fa.accept_26_6_2_13_1_14894 58 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 247 (accept_3_3 56 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 247
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 54 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 247 (accept_3_3 53 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 247 (accept_3_3 50 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 247 (accept_3_3 47 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 247 (accept_3_3 44 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 247 (Polychromatic418967fa.accept_10_3_6_7_1_2188 43 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 247 (accept_3_3 41 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 247 (accept_3_3 38 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 247
  (Polychromatic418967fa.accept_15_6_1_7_1_4079 36 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 247 (accept_3_3 35 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 247 (accept_3_3 32 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 247 (accept_3_3 29 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 247 (accept_3_3 26 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 247 (accept_3_3 23 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 247 (Polychromatic418967fa.accept_27_22_25_4_1_14893 22 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 247 (accept_3_3 20 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 106 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 247
  (Polychromatic418967fa.accept_24_18_10_7_1_8157 18 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 106 247 (accept_3_3 17 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 106 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 106 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 106 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 106 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 247 (accept_3_3 14 106 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 247 (accept_3_3 11 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 247 (accept_3_3 8 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 247 (Polychromatic418967fa.accept_21_7_1_16_1_9032 7 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 247 (accept_3_3 5 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 106 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 247 (accept_3_3 2 106 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 247 (allA_succ_of_accept 104 105 247 (accept_3_3 104 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 247 (Polychromatic418967fa.accept_10_3_5_7_1_330 103 105 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 105
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 247 (accept_3_3 101 105
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 247
  (Polychromatic418967fa.accept_6_4_3_1_1_57 100 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 247 (Polychromatic418967fa.accept_12_3_9_7_1_472 99 105 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 247 (accept_3_3 98 105 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 105 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 97 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 247 (Polychromatic418967fa.accept_14_12_7_9_1_726
  96 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 247 (accept_3_3 95
  105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 94 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 105 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 247 (accept_3_3 92 105 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 105 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 90
  105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 247 (accept_3_3 89
  105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 247
  (Polychromatic418967fa.accept_6_4_3_1_1_57 88 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 105 247 (Polychromatic418967fa.accept_11_10_6_5_1_1239 87 105 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 247 (accept_3_3 86 105 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 105 247 (Polychromatic418967fa.accept_22_19_17_5_1_10390 85 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 105 247 (accept_3_3 83 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 105 247 (Polychromatic418967fa.accept_25_6_5_22_1_14892 81 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 247 (accept_3_3 80 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 105 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 105 247 (accept_3_3 77 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 105 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 105 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 247 (accept_3_3 74 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 247
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 105 247 (accept_3_3 71 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 105 247 (Polychromatic418967fa.accept_17_1_3_9_1_958 69 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 247 (accept_3_3 68 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 247 (Polychromatic418967fa.accept_11_1_6_5_1_1732 67 105
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 247 (accept_3_3 65 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 105 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 105 247 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 247 (accept_3_3 62 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 105 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 247
  (Polychromatic418967fa.accept_24_12_9_7_1_13282 60 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 105 247 (accept_3_3 59 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 105 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 247 (accept_3_3 56 105 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 55
  105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 247 (accept_3_3 53 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 247 (Polychromatic418967fa.accept_12_3_9_7_1_472 51 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 247 (accept_3_3 50 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 247 (Polychromatic418967fa.accept_20_9_5_7_1_6336 49 105
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 247 (accept_3_3 47 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 247 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 247 (accept_3_3 44 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 105 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 247 (accept_3_3 41 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 247 (accept_3_3 38 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 247
  (Polychromatic418967fa.accept_22_14_17_5_1_13436 36 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 247 (accept_3_3 35 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 247 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 105
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 247 (accept_3_3 32 105
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 247
  (Polychromatic418967fa.accept_25_6_5_22_1_14892 31 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 247 (accept_3_3 29 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 105 247 (accept_3_3 26 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 105 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 105 247 (Polychromatic418967fa.accept_16_8_9_7_1_768 24 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 247 (accept_3_3 23 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 105 247 (accept_3_3 20 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 105 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 247 (accept_3_3 17 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 105 247 (accept_3_3 14 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 105 247 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 105 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 247 (accept_3_3 11 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 247
  (Polychromatic418967fa.accept_20_9_5_7_1_6336 9 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 247 (accept_3_3 8 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  105 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 247 (accept_3_3 5 105 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 247 (accept_3_3 2 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 105 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 247 (allA_of_3_1 104 104 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 247
  (allA_succ_of_accept 102 103 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 102 103 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 247 (accept_3_3 101 103 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 247 (Polychromatic418967fa.accept_17_15_1_9_1_10058 100 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 247
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 99 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 247 (accept_3_3 98 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 247 (Polychromatic418967fa.accept_21_13_19_16_1_721 97 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 247 (Polychromatic418967fa.accept_10_6_3_7_1_2197 96 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 247 (accept_3_3 95 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 94 103 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 247
  (Polychromatic418967fa.accept_17_8_1_9_1_7738 93 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 247 (accept_3_3 92 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 247 (Polychromatic418967fa.accept_14_7_5_9_1_2911 91 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 247 (Polychromatic418967fa.accept_20_10_3_7_1_10761 90 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 247 (accept_3_3 89 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 88 103 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 247 (accept_3_3 86 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 247 (Polychromatic418967fa.accept_10_5_3_7_1_1108 85 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 247 (Polychromatic418967fa.accept_10_4_3_7_1_1110 84 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 247 (accept_3_3 83 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 247 (Polychromatic418967fa.accept_23_13_11_17_1_10011 82
  103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 247 (accept_3_3 80 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 247 (Polychromatic418967fa.accept_23_10_11_17_1_14891 79 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 103 247 (Polychromatic418967fa.accept_17_10_1_9_1_11372 78 103 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 247 (accept_3_3 77 103 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 247 (Polychromatic418967fa.accept_10_6_3_7_1_2197
  76 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 247
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 75 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 247 (accept_3_3 74 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 73 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 247 (Polychromatic418967fa.accept_27_18_22_4_1_9203 72 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 247 (accept_3_3 71 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 247 (Polychromatic418967fa.accept_20_10_3_7_1_10761 70 103
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 247
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 69 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 247 (accept_3_3 68 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 103 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 247 (accept_3_3 65 103 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 247 (Polychromatic418967fa.accept_10_4_3_7_1_1110 64 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 247
  (Polychromatic418967fa.accept_14_7_5_9_1_2911 63 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 247 (accept_3_3 62 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 247 (Polychromatic418967fa.accept_17_10_1_9_1_11372 61 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 103 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 247 (accept_3_3 59 103 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 247 (Polychromatic418967fa.accept_25_8_3_22_1_14890 58 103 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 247
  (Polychromatic418967fa.accept_25_7_3_22_1_14889 57 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 103 247 (accept_3_3 56 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 103 247 (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 103 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 247 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 103
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 247 (accept_3_3 53 103
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 52 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 103 247 (Polychromatic418967fa.accept_15_6_13_7_1_222 51 103 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 247 (accept_3_3 50 103 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 103 247 (Polychromatic418967fa.accept_14_7_5_9_1_2911 49 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 247
  (Polychromatic418967fa.accept_22_4_15_5_1_14888 48 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 103 247 (accept_3_3 47 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 103 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 103 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 103 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 247 (accept_3_3 44 103 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 247 (Polychromatic418967fa.accept_11_10_4_5_1_359
  43 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 247
  (Polychromatic418967fa.accept_17_8_1_9_1_7738 42 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 247 (accept_3_3 41 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 247 (Polychromatic418967fa.accept_25_15_3_22_1_14887 40 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 247 (accept_3_3 38 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 247 (Polychromatic418967fa.accept_17_3_1_9_1_9012 37 103
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 247
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 247 (accept_3_3 35 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 247 (Polychromatic418967fa.accept_10_4_3_7_1_1110 34 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 247 (Polychromatic418967fa.accept_22_11_15_5_1_11814 33 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 247 (accept_3_3 32 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 103 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 247
  (Polychromatic418967fa.accept_20_10_3_7_1_10761 30 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 103 247 (accept_3_3 29 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 103 247 (Polychromatic418967fa.accept_23_5_11_17_1_14886 28 103 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 247
  (Polychromatic418967fa.accept_17_10_1_9_1_11372 27 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 103 247 (accept_3_3 26 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 103 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 103 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 103 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 247 (accept_3_3 23 103 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 247
  (Polychromatic418967fa.accept_21_1_19_16_1_2901 22 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 247 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 247 (accept_3_3 20 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 247 (Polychromatic418967fa.accept_23_19_11_17_1_14885 19
  103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 247 (accept_3_3 17 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 247 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 247 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 247 (accept_3_3 14 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 247 (Polychromatic418967fa.accept_21_13_19_16_1_721 13 103
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 247
  (Polychromatic418967fa.accept_22_12_15_5_1_10376 12 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 103 247 (accept_3_3 11 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 103 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 103 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 247 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 103
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 247 (accept_3_3 8 103 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 247 (Polychromatic418967fa.accept_14_7_5_9_1_2911
  7 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 247
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 247 (accept_3_3 5 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 103 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 103 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 247 (accept_3_3 2 103 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 247 (Polychromatic418967fa.accept_21_1_19_16_1_2901 1 103 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 247 (allA_succ_of_accept 101 102 247 (accept_3_3 101 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 102 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 100 102 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 102 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 99 102
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 247 (accept_3_3 98 102
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9
  97 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 96 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 247 (accept_3_3 95 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 102 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 94 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 247 (accept_3_3 92 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 90 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 102 247 (accept_3_3 89 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 102 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 102 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 247 (accept_3_3 86 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 247
  (Polychromatic418967fa.accept_10_4_2_7_1_373 84 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 102 247 (accept_3_3 83 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 102 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 82 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 247 (accept_3_3 80 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 102 247 (accept_3_3 77 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 102 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 76 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 102 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 247 (accept_3_3 74 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 247
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 102 247 (accept_3_3 71 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 102 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 247 (accept_3_3 68 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 247 (Polychromatic418967fa.accept_25_17_2_22_1_7827 67 102 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 247
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 66 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 102 247 (accept_3_3 65 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 102 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 102 247 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 247 (accept_3_3 62 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 102 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 247 (accept_3_3 59 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 102 247 (Polychromatic418967fa.accept_14_2_4_9_1_2121 58 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 247 (accept_3_3 56 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 102 247 (accept_3_3 53 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 102 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 102 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 247 (accept_3_3 50 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 102 247 (accept_3_3 47 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 102 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 247 (accept_3_3 44 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 247 (accept_3_3 41 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 247 (accept_3_3 38 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 247
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 102 247 (accept_3_3 35 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 102 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 247 (accept_3_3 32 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 247 (Polychromatic418967fa.accept_16_15_6_7_1_4512 31 102 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 247
  (Polychromatic418967fa.accept_11_8_3_5_1_355 30 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 102 247 (accept_3_3 29 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 102 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 102 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 247 (accept_3_3 26 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 247 (accept_3_3 23 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 247 (Polychromatic418967fa.accept_27_22_21_4_1_11191 22 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 247 (accept_3_3 20 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 102 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 247
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 247 (accept_3_3 17 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 247 (accept_3_3 14 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 247 (accept_3_3 11 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 247 (accept_3_3 8 102 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 247 (accept_3_3 5 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 102 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 247 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 247 (accept_3_3 2 102 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 247 (allA_of_3_1 101 101 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 247 (allA_succ_of_accept 99
  100 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 100 247 (accept_3_3 98 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 100 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 100 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 100 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 100 247 (accept_3_3 95 100 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 100 247 (Polychromatic418967fa.accept_11_6_1_5_1_2388
  94 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 100 247 (accept_3_3 92 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 100 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 91 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 100 247 (Polychromatic418967fa.accept_22_2_12_5_1_14884 90 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 100 247 (accept_3_3 89 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 100 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 100 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 100 247 (accept_3_3 86 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 100 247 (Polychromatic418967fa.accept_22_19_12_5_1_11813 85 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 100 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 100 247 (accept_3_3 83 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 100 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 100
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 100 247 (accept_3_3 80 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 100 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 100 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 100 247 (accept_3_3 77 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 100 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 76 100 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 100 247 (accept_3_3 74 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 100 247 (Polychromatic418967fa.accept_18_1_10_13_1_500 73 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 100 247 (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 100 247 (accept_3_3 71 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 100 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 100 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 100 247 (accept_3_3 68 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 100 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 100 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 100 247 (accept_3_3 65 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 100 247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 64 100 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 100 247 (accept_3_3 62 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 100 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 100 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 100 247 (accept_3_3 59 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 100 247 (accept_3_3 56 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 100 247 (Polychromatic418967fa.accept_18_1_10_13_1_500 55 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 100 247 (Polychromatic418967fa.accept_31_23_7_30_1_12809 54 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 100 247 (accept_3_3 53 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 100 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 100 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 100 247 (accept_3_3 50 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 100 247 (Polychromatic418967fa.accept_14_7_2_9_1_2093 49 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 100 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 247 (accept_3_3 47 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 100 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 100 247 (accept_3_3 44 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 100 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 100 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 100 247 (accept_3_3 41 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 100 247 (Polychromatic418967fa.accept_16_8_4_7_1_3390 40 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 100 247 (accept_3_3 38 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 100 247 (Polychromatic418967fa.accept_18_1_10_13_1_500 37 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 100 247 (Polychromatic418967fa.accept_24_12_4_7_1_14883 36 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 247 (accept_3_3 35 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 100 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 100 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 100 247 (accept_3_3 32 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 100 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 31 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 100 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 247 (accept_3_3 29 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 247 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 247 (accept_3_3 26 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 100 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 100 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 247 (accept_3_3 23 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 247 (accept_3_3 20 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 247 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 247 (accept_3_3 17 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 100 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 247 (accept_3_3 14 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 247 (Polychromatic418967fa.accept_16_13_4_7_1_1537 13 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 247 (accept_3_3 11 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 247 (accept_3_3 8 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 247 (accept_3_3 5 100 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 247 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 100 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 247 (accept_3_3 2 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 100 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  247 (allA_succ_of_accept 98 99 247 (accept_3_3 98 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 97 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 247 (Polychromatic418967fa.accept_18_6_9_13_1_3320 96 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 247 (accept_3_3 95 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 99 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 93 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 247 (accept_3_3 92 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 247 (Polychromatic418967fa.accept_15_1_9_7_1_3130 91 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 247 (accept_3_3 89 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 87 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 247 (accept_3_3 86 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 247 (Polychromatic418967fa.accept_21_1_15_16_1_5891 85 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 247 (accept_3_3 83 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 247 (accept_3_3 80 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 247 (Polychromatic418967fa.accept_16_15_3_7_1_3389 79 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 247 (Polychromatic418967fa.accept_10_8_9_7_1_1118 78 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 247 (accept_3_3 77 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 247
  (Polychromatic418967fa.accept_16_11_3_7_1_2375 75 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 247 (accept_3_3 74 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 73 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 247 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 247 (accept_3_3 71 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 247 (accept_3_3 68 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 247 (Polychromatic418967fa.accept_24_19_3_7_1_13315 67 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 247 (accept_3_3 65 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 247
  (Polychromatic418967fa.accept_16_15_3_7_1_3389 63 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 247 (accept_3_3 62 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 247 (Polychromatic418967fa.accept_15_1_9_7_1_3130 61 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 247 (accept_3_3 59 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 247 (accept_3_3 56 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 247 (Polychromatic418967fa.accept_26_2_21_13_1_14882 54 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 247 (accept_3_3 53 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 247
  (Polychromatic418967fa.accept_21_9_15_16_1_4328 51 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 247 (accept_3_3 50 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 247 (Polychromatic418967fa.accept_27_22_18_4_1_11207 49 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 247 (accept_3_3 47 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 247 (accept_3_3 44 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 247 (Polychromatic418967fa.accept_15_13_9_7_1_2194 43 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 247 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 247 (accept_3_3 41 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 247
  (Polychromatic418967fa.accept_17_5_14_9_1_5104 39 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 247 (accept_3_3 38 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 247 (Polychromatic418967fa.accept_20_17_19_7_1_4767 37 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 247 (accept_3_3 35 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 247 (accept_3_3 32 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 247 (Polychromatic418967fa.accept_20_10_19_7_1_14881 30 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 247 (accept_3_3 29 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 247 (accept_3_3 26 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 247 (Polychromatic418967fa.accept_16_9_3_7_1_6883 25 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 247 (accept_3_3 23 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 247 (accept_3_3 20 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 247 (Polychromatic418967fa.accept_24_19_3_7_1_13315 19 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 247 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 247 (accept_3_3 17 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 247
  (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 247 (accept_3_3 14 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 247 (accept_3_3 11 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 247 (accept_3_3 8 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  247 (Polychromatic418967fa.accept_22_7_11_5_1_13461 7 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 247 (accept_3_3 5 99 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 247 (accept_3_3 2 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  247 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1 99 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  247 (allA_of_3_1 98 98 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 247 (allA_succ_of_accept 96 97 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 96 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 247 (accept_3_3 95 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 93 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 247 (accept_3_3 92 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 247 (accept_3_3 89 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 88 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 247 (accept_3_3 86 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 85 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 247 (accept_3_3 83 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 247 (accept_3_3 80 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 247 (Polychromatic418967fa.accept_20_19_17_7_1_6299 79 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 247 (accept_3_3 77 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 247 (Polychromatic418967fa.accept_18_4_7_13_1_3303 76 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 247 (accept_3_3 74 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 247
  (Polychromatic418967fa.accept_16_8_1_7_1_2355 72 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 247 (accept_3_3 71 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 247 (accept_3_3 68 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 247 (accept_3_3 65 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 247 (Polychromatic418967fa.accept_26_11_19_13_1_14880 63 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 247 (accept_3_3 62 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 247 (Polychromatic418967fa.accept_21_19_13_16_1_7317 61 97
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 247 (accept_3_3 59 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 247 (accept_3_3 56 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 247 (accept_3_3 53 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 247 (accept_3_3 50 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 247 (Polychromatic418967fa.accept_20_9_17_7_1_4748 49 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 247 (accept_3_3 47 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 247 (accept_3_3 44 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 247 (accept_3_3 41 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 247 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 247 (accept_3_3 38 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 247 (accept_3_3 35 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 247 (accept_3_3 32 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 247 (accept_3_3 29 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 247 (Polychromatic418967fa.accept_21_6_13_16_1_7353 27 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 247 (accept_3_3 26 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 97 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 247 (accept_3_3 23 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 247 (accept_3_3 20 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 247 (accept_3_3 17 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 247 (Polychromatic418967fa.accept_20_16_17_7_1_7845 16 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 247 (accept_3_3 14 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 247 (Polychromatic418967fa.accept_24_13_1_7_1_8147 13 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 247 (accept_3_3 11 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 247 (Polychromatic418967fa.accept_20_9_17_7_1_4748 9 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 247 (accept_3_3 8 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 247 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 97 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 247 (accept_3_3 5 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  247 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 97 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 97 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 247 (accept_3_3 2 97 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 97 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 247
  (allA_succ_of_accept 95 96 247 (accept_3_3 95 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  96 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 94 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 96 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 96 247 (accept_3_3 92 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 247
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 90 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 96 247 (accept_3_3 89 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  96 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 88 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 96 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 247 (accept_3_3 86 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 247 (Polychromatic418967fa.accept_22_19_8_5_1_11841 85 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 247 (accept_3_3 83 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  96 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 247 (accept_3_3 80 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 247
  (Polychromatic418967fa.accept_29_20_9_15_1_14879 78 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 96 247 (accept_3_3 77 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 247 (Polychromatic418967fa.accept_15_1_6_7_1_6282 76 96 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 96 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 96 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 247 (accept_3_3 74 96 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 73
  96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 247
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 72 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 247 (accept_3_3 71 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  96 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 247 (Polychromatic418967fa.accept_11_3_8_5_1_336 69 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 247 (accept_3_3 68 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 66 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 247 (accept_3_3 65 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 247 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 247 (accept_3_3 62 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 247 (accept_3_3 59 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 247 (Polychromatic418967fa.accept_11_3_8_5_1_336 58 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 247 (accept_3_3 56 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 247
  (Polychromatic418967fa.accept_17_3_11_9_1_5100 54 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 247 (accept_3_3 53 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 247 (Polychromatic418967fa.accept_10_1_6_7_1_710 51 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 247 (accept_3_3 50 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 247 (Polychromatic418967fa.accept_14_7_12_9_1_2926 49 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 247 (accept_3_3 47 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 247 (accept_3_3 44 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 247
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 42 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 247 (accept_3_3 41 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 247 (Polychromatic418967fa.accept_25_15_21_22_1_14878 40 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 247 (accept_3_3 38 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 247
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 247 (accept_3_3 35 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 247 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 247 (accept_3_3 32 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 247 (accept_3_3 29 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 247 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 247 (accept_3_3 26 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 96 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 247 (accept_3_3 23 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 247 (Polychromatic418967fa.accept_29_22_9_15_1_14877 22 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 247 (accept_3_3 20 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 247 (accept_3_3 17 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 247 (Polychromatic418967fa.accept_22_15_8_5_1_14876 15 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 247 (accept_3_3 14 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 247 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 96 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 247 (accept_3_3 11 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 247 (Polychromatic418967fa.accept_18_9_6_13_1_4499 9 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 247 (accept_3_3 8 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 247
  (Polychromatic418967fa.accept_20_6_16_7_1_9232 6 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 247 (accept_3_3 5 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  247 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 96 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 247 (accept_3_3 2 96 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 96 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 247
  (allA_of_3_1 95 95 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 247 (allA_succ_of_accept 93 94 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 94 247 (accept_3_3 92 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  94 247 (Polychromatic418967fa.accept_10_1_4_7_1_374 91 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 94 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 247 (accept_3_3 89 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 94 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 94 247 (accept_3_3 86 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  94 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 94 247 (Polychromatic418967fa.accept_16_4_14_7_1_5641 84 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 247 (accept_3_3 83 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 82 94 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 247 (accept_3_3 80 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 247 (Polychromatic418967fa.accept_16_15_14_7_1_10555 79 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 247 (accept_3_3 77 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 76 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 247 (accept_3_3 74 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 247 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 247 (accept_3_3 71 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 247 (Polychromatic418967fa.accept_15_10_4_7_1_3127 70 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 247 (accept_3_3 68 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 247 (Polychromatic418967fa.accept_11_1_6_5_1_1732 67 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 247 (Polychromatic418967fa.accept_21_3_10_16_1_4340 66 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 247 (accept_3_3 65 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 94 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 247 (accept_3_3 62 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 247 (Polychromatic418967fa.accept_27_6_13_4_1_13037 60 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 247 (accept_3_3 59 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 247 (Polychromatic418967fa.accept_16_10_14_7_1_2372 58 94
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 247 (accept_3_3 56 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 247 (accept_3_3 53 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 247 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 247 (accept_3_3 50 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 247 (accept_3_3 47 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 247 (Polychromatic418967fa.accept_18_10_4_13_1_3296 46 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 247 (accept_3_3 44 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 247 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 247 (accept_3_3 41 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 247 (accept_3_3 38 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 247 (accept_3_3 35 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 247 (accept_3_3 32 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 247 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 247 (Polychromatic418967fa.accept_21_9_10_16_1_7327 30 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 247 (accept_3_3 29 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 94 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 247 (accept_3_3 26 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 247 (Polychromatic418967fa.accept_21_3_10_16_1_4340 24 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 247 (accept_3_3 23 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 94 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 247 (accept_3_3 20 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 247 (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 247 (accept_3_3 17 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 247 (accept_3_3 14 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 247 (accept_3_3 11 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 247 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 247 (accept_3_3 8 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  247 (Polychromatic418967fa.accept_18_7_4_13_1_3315 7 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 94 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 247 (accept_3_3 5 94 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 94 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 94 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 94 247 (accept_3_3 2 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94
  247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 93 247 (allA_succ_of_accept 92 93 247 (accept_3_3 92 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 93 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 93 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 247 (accept_3_3 89 93 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 88
  93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 247 (accept_3_3 86 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 247 (Polychromatic418967fa.accept_10_5_3_7_1_1108 85 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 247 (Polychromatic418967fa.accept_10_4_3_7_1_1110 84 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 247 (accept_3_3 83 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 247
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 81 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 247 (accept_3_3 80 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 247 (accept_3_3 77 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 247
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 75 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 247 (accept_3_3 74 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 247 (Polychromatic418967fa.accept_15_12_3_7_1_4123 72 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 247 (accept_3_3 71 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 247 (accept_3_3 68 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 247 (Polychromatic418967fa.accept_17_16_8_9_1_1772 67 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 247 (accept_3_3 65 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 247 (accept_3_3 62 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 247 (accept_3_3 59 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 247
  (Polychromatic418967fa.accept_15_12_3_7_1_4123 57 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 247 (accept_3_3 56 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 247 (accept_3_3 53 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 247 (accept_3_3 50 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 247 (Polychromatic418967fa.accept_15_4_3_7_1_713 49 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 247 (Polychromatic418967fa.accept_18_12_3_13_1_4494 48 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 247 (accept_3_3 47 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 247
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 247 (accept_3_3 44 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 247 (accept_3_3 41 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 247 (accept_3_3 38 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 247 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 247 (accept_3_3 35 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 247 (accept_3_3 32 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 247 (Polychromatic418967fa.accept_21_10_9_16_1_9073 31 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 247 (accept_3_3 29 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 247 (accept_3_3 26 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 247 (accept_3_3 23 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 247
  (Polychromatic418967fa.accept_25_21_18_22_1_14875 21 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 247 (accept_3_3 20 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 93 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 247 (accept_3_3 17 93 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 247 (accept_3_3 14 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 247 (Polychromatic418967fa.accept_21_13_9_16_1_5860 13 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 247 (Polychromatic418967fa.accept_15_12_3_7_1_4123 12 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 247 (accept_3_3 11 93 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 247
  (Polychromatic418967fa.accept_16_9_13_7_1_1509 9 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 247 (accept_3_3 8 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 247 (accept_3_3 5 93 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 247 (Polychromatic418967fa.accept_12_3_9_7_1_472 3
  93 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 247 (accept_3_3 2 93 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 93
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 247
  (allA_of_3_1 92 92 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 247 (allA_succ_of_accept 90 91 247
  (Polychromatic418967fa.accept_20_10_11_7_1_4796 90 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 247 (accept_3_3 89 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 87 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 247 (accept_3_3 86 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 247 (Polychromatic418967fa.accept_11_8_3_5_1_355 85 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 247
  (Polychromatic418967fa.accept_8_4_3_7_1_491 84 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 91 247 (accept_3_3 83 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 247 (Polychromatic418967fa.accept_14_12_7_9_1_726 82 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 247 (Polychromatic418967fa.accept_15_6_1_7_1_4079 81 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 247 (accept_3_3 80 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 91 247 13 6 7 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 91 247 (accept_3_3 77 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 91 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 76 91 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 75 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 247 (accept_3_3 74 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 247 (Polychromatic418967fa.accept_21_10_7_16_1_9036 73 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 247 (Polychromatic418967fa.accept_14_2_7_9_1_2937 72 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 247 (accept_3_3 71 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 69 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 247 (accept_3_3 68 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 247 (Polychromatic418967fa.accept_16_3_11_7_1_770 67 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 91 247 13 5 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 91 247 (Polychromatic418967fa.accept_10_4_1_7_1_371 64
  91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 247
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 247 (accept_3_3 62 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 247 (accept_3_3 59 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 247 (Polychromatic418967fa.accept_14_2_7_9_1_2937 58 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 247 (accept_3_3 56 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 55 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 247 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 247 (accept_3_3 53 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 91 247 13 4 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 91 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 247 (accept_3_3 50 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 247 (Polychromatic418967fa.accept_17_15_6_9_1_13743 49 91
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 247 (accept_3_3 47 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 247 (Polychromatic418967fa.accept_10_6_1_7_1_342 46 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 247 (Polychromatic418967fa.accept_21_3_7_16_1_11967 45 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 247 (accept_3_3 44 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 91 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 247 (accept_3_3 41 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 247 (Polychromatic418967fa.accept_14_12_7_9_1_726 40 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 91 247 13 3 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 91 247 (accept_3_3 38 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 91 247 (Polychromatic418967fa.accept_16_5_11_7_1_5635 37 91 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 91 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 247 (accept_3_3 35 91 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 34
  91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 247 (accept_3_3 32 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 247 (Polychromatic418967fa.accept_16_15_11_7_1_6951 31 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 247 (accept_3_3 29 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 247
  (Polychromatic418967fa.accept_21_6_7_16_1_9035 27 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 91 247 13 2 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 91 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 91 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 247 (accept_3_3 23 91 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 247 (Polychromatic418967fa.accept_21_1_7_16_1_5859
  22 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 247 (accept_3_3 20 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 247 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 247 (Polychromatic418967fa.accept_16_2_11_7_1_2352 18 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 247 (accept_3_3 17 91 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 247 (accept_3_3 14 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 91
  247 13 1 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12
  91 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 91 247 (accept_3_3 11 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 91 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 10 91 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 247 (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 91 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 247 (accept_3_3 8 91 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7
  91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 247 (accept_3_3 5 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  247 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 91 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 91 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 247 (accept_3_3 2 91 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 247 (Polychromatic418967fa.accept_20_1_11_7_1_10755 1 91 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 247
  (allA_succ_of_accept 89 90 247 (accept_3_3 89 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  90 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 88 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 247 (accept_3_3 86 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 247
  (Polychromatic418967fa.accept_22_18_2_5_1_14819 84 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 247 (accept_3_3 83 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  90 247 (Polychromatic418967fa.accept_17_14_5_9_1_7766 82 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 90 247 (accept_3_3 80 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 247 (Polychromatic418967fa.accept_20_19_10_7_1_7877 79 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 78 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 90 247 (accept_3_3 77 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  90 247 (Polychromatic418967fa.accept_21_13_6_16_1_9023 76 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 90 247 (Polychromatic418967fa.accept_17_7_5_9_1_7763 75 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 247 (accept_3_3 74 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 247
  (Polychromatic418967fa.accept_21_9_6_16_1_5857 72 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 90 247 (accept_3_3 71 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  90 247 (Polychromatic418967fa.accept_21_7_6_16_1_5834 70 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 247 (accept_3_3 68 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 90 247 (accept_3_3 65 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  90 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 90 247 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 247 (accept_3_3 62 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 90 247 (accept_3_3 59 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  90 247 (Polychromatic418967fa.accept_17_7_5_9_1_7763 58 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 247 (accept_3_3 56 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 247 (Polychromatic418967fa.accept_20_15_10_7_1_7878 55 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 247
  (Polychromatic418967fa.accept_21_12_6_16_1_5855 54 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 90 247 (accept_3_3 53 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  90 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 90 247 (Polychromatic418967fa.accept_16_3_10_7_1_4518 51 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 247 (accept_3_3 50 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 247
  (Polychromatic418967fa.accept_17_14_5_9_1_7766 48 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 90 247 (accept_3_3 47 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  90 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 247 (accept_3_3 44 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 247
  (Polychromatic418967fa.accept_23_19_21_17_1_4957 42 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 90 247 (accept_3_3 41 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 247 (Polychromatic418967fa.accept_22_18_2_5_1_14819 40 90 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 90 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 247 (accept_3_3 38 90 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 247 (accept_3_3 35 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  90 247 (Polychromatic418967fa.accept_21_13_6_16_1_9023 34 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 247 (accept_3_3 32 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 247
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 247 (accept_3_3 29 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 247 (Polychromatic418967fa.accept_20_8_10_7_1_6291 28 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 247 (Polychromatic418967fa.accept_23_4_21_17_1_14874 27 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 247 (accept_3_3 26 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 247 (accept_3_3 23 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  90 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 247 (accept_3_3 20 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 247 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 90 247 (accept_3_3 17 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  90 247 (Polychromatic418967fa.accept_24_16_18_7_1_14873 16 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 90 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 247 (accept_3_3 14 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 247
  (Polychromatic418967fa.accept_17_12_5_9_1_6372 12 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 247 (accept_3_3 11 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 247 (accept_3_3 8 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 247 (Polychromatic418967fa.accept_17_7_5_9_1_7763 7 90 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 247
  (Polychromatic418967fa.accept_23_6_21_17_1_14872 6 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 247 (accept_3_3 5 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  247 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 90 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 90 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 90 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 247 (accept_3_3 2 90 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 90 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 247
  (allA_of_3_1 89 89 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 247 (allA_succ_of_accept 87 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 88 247 (accept_3_3 86 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  88 247 (Polychromatic418967fa.accept_10_5_8_7_1_2174 85 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 88 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 247 (accept_3_3 83 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 82 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 88 247 (accept_3_3 80 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  88 247 (Polychromatic418967fa.accept_10_9_8_7_1_714 79 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 88 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 247 (accept_3_3 77 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 76 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 247 (accept_3_3 74 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 247 (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 247 (accept_3_3 71 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 247 (accept_3_3 68 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 247 (Polychromatic418967fa.accept_23_21_19_17_1_11738 67 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 88 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 247 (accept_3_3 65 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 88 247 (accept_3_3 62 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  88 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 88 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 247 (accept_3_3 59 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 247 (accept_3_3 56 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 247 (accept_3_3 53 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 247 (Polychromatic418967fa.accept_16_4_8_7_1_3396 52 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 247 (accept_3_3 50 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 247 (Polychromatic418967fa.accept_10_9_8_7_1_714 49 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 247 (accept_3_3 47 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 247 (accept_3_3 44 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 247 (Polychromatic418967fa.accept_23_20_19_17_1_14871 43 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 247 (accept_3_3 41 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 247 (accept_3_3 38 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 247 (Polychromatic418967fa.accept_15_6_13_7_1_222 36 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 247 (accept_3_3 35 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 247 (accept_3_3 32 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 247 (Polychromatic418967fa.accept_16_15_8_7_1_3407 31 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 247 (accept_3_3 29 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 247 (accept_3_3 26 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 247 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 247 (accept_3_3 23 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 247 (accept_3_3 20 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 247 (Polychromatic418967fa.accept_17_1_3_9_1_958 18 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 247 (accept_3_3 17 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 247 (Polychromatic418967fa.accept_14_2_4_9_1_2121 16 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 247 (accept_3_3 14 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 247 (accept_3_3 11 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 247 (accept_3_3 8 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  247 (Polychromatic418967fa.accept_21_7_4_16_1_5888 7 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 88 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 247 (accept_3_3 5 88 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 88 247 (Polychromatic418967fa.accept_16_4_8_7_1_3396 4 88 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 88 247 (accept_3_3 2 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88
  247 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 88 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87
  247 (allA_succ_of_accept 86 87 247 (accept_3_3 86 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 87 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 85 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 247 (accept_3_3 83 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 247
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 81 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 247 (accept_3_3 80 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 247 (accept_3_3 77 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 247 (accept_3_3 74 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 247 (Polychromatic418967fa.accept_11_6_10_5_1_341 72 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 247 (accept_3_3 71 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 247 (accept_3_3 68 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 247 (Polychromatic418967fa.accept_22_1_21_5_1_10380 67 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 247 (accept_3_3 65 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 247
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 63 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 247 (accept_3_3 62 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 247 (Polychromatic418967fa.accept_21_18_3_16_1_5833 60 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 247 (accept_3_3 59 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 87 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 247 (accept_3_3 56 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 247 (accept_3_3 53 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 247
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 51 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 247 (accept_3_3 50 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 247 (Polychromatic418967fa.accept_15_4_12_7_1_3115 49 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 247 (accept_3_3 47 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 247 (accept_3_3 44 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 247 (Polychromatic418967fa.accept_22_20_21_5_1_13404 42 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 247 (accept_3_3 41 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 247 (accept_3_3 38 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 247 (accept_3_3 35 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 247 (accept_3_3 32 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 247 (Polychromatic418967fa.accept_21_10_3_16_1_5909 31 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 247 (accept_3_3 29 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 247 (accept_3_3 26 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 247 (Polychromatic418967fa.accept_17_7_2_9_1_6396 24 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 247 (accept_3_3 23 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 247 (accept_3_3 20 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 247 (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 247 (accept_3_3 17 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 247 (accept_3_3 14 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 247 (accept_3_3 11 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 87 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 247 (accept_3_3 8 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 87 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 247 (accept_3_3 5 87 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  87 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 247 (accept_3_3 2 87 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 87
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 247
  (allA_of_3_1 86 86 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 247 (allA_succ_of_accept 84 85 247
  (Polychromatic418967fa.accept_23_15_16_17_1_14870 84 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 85 247 (accept_3_3 83 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 85 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 247 (Polychromatic418967fa.accept_31_19_23_30_1_14869 81 85
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 247 (accept_3_3 80 85 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 247 (Polychromatic418967fa.accept_11_2_8_5_1_1219
  79 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 247 (accept_3_3 77 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 247 (Polychromatic418967fa.accept_16_11_5_7_1_2395 75 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 247 (accept_3_3 74 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 73 85 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 247
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 247 (accept_3_3 71 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 247 (accept_3_3 68 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 247 (Polychromatic418967fa.accept_24_19_13_7_1_14868 67 85 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 247 (accept_3_3 65 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 247 (Polychromatic418967fa.accept_14_8_1_9_1_2085 64 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 247 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 247 (accept_3_3 62 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 61 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 247
  (Polychromatic418967fa.accept_16_12_5_7_1_2360 60 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 247 (accept_3_3 59 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 247 (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 247 (accept_3_3 56 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 247 (accept_3_3 53 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 247 (Polychromatic418967fa.accept_25_1_10_22_1_14867 51 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 247 (accept_3_3 50 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 49 85
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 247 (accept_3_3 47 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 247 (accept_3_3 44 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 247 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 247 (accept_3_3 41 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 247 (Polychromatic418967fa.accept_21_19_1_16_1_1665 40 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 247 (Polychromatic418967fa.accept_22_17_19_5_1_7044 39 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 247 (accept_3_3 38 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 247 (Polychromatic418967fa.accept_25_12_10_22_1_14866 37 85
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 247
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 247 (accept_3_3 35 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 247 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 247 (accept_3_3 32 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 247 (accept_3_3 29 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 247 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 247 (accept_3_3 26 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 247 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 247 (accept_3_3 23 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 247 (Polychromatic418967fa.accept_24_21_13_7_1_8122 21 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 247 (accept_3_3 20 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 85
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 247 (accept_3_3 17 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 247 (Polychromatic418967fa.accept_20_15_5_7_1_4791 15 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 247 (accept_3_3 14 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 85 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 247
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 247 (accept_3_3 11 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 247 (Polychromatic418967fa.accept_20_9_5_7_1_6336 9 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 247 (accept_3_3 8 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 247 (Polychromatic418967fa.accept_21_7_1_16_1_9032 7 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 247 (accept_3_3 5 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 85 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 247 (accept_3_3 2 85 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 85 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 247
  (allA_succ_of_accept 83 84 247 (accept_3_3 83 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 247 (Polychromatic418967fa.accept_10_1_4_7_1_374 81 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 247 (accept_3_3 80 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 84 247 (accept_3_3 77 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  84 247 (Polychromatic418967fa.accept_15_1_9_7_1_3130 76 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 84 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 247 (accept_3_3 74 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 247
  (Polychromatic418967fa.accept_10_2_4_7_1_352 72 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 247 (accept_3_3 71 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 247 (accept_3_3 68 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 247
  (Polychromatic418967fa.accept_23_20_15_17_1_14865 66 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 84 247 (accept_3_3 65 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 84 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 84 247 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 84 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 247 (accept_3_3 62 84 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 61
  84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 247 (accept_3_3 59 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 247 (Polychromatic418967fa.accept_15_13_9_7_1_2194 58 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 247 (Polychromatic418967fa.accept_17_6_16_9_1_5129 57 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 247 (accept_3_3 56 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 84 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 247
  (Polychromatic418967fa.accept_23_8_15_17_1_14864 54 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 84 247 (accept_3_3 53 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 84 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 84 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 84 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 247 (accept_3_3 50 84 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 247
  (Polychromatic418967fa.accept_31_18_22_30_1_14863 49 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 84 247 (Polychromatic418967fa.accept_22_4_18_5_1_5358 48 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 247 (accept_3_3 47 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 84 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 84 247
  (Polychromatic418967fa.accept_16_13_4_7_1_1537 45 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 84 247 (accept_3_3 44 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  84 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 84 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 247 (accept_3_3 41 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 247 (Polychromatic418967fa.accept_16_8_4_7_1_3390 40 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 84 247
  (Polychromatic418967fa.accept_18_3_12_13_1_3307 39 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 84 247 (accept_3_3 38 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  84 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 84 247 (Polychromatic418967fa.accept_32_4_20_23_1_14862 36 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 247 (accept_3_3 35 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 84 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 84 247 (accept_3_3 32 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  84 247 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 84 247 (Polychromatic418967fa.accept_16_14_4_7_1_2380 30 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 247 (accept_3_3 29 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 84 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 84 247
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 84 247 (accept_3_3 26 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  84 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 84 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 247 (accept_3_3 23 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 247 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 84 247
  (Polychromatic418967fa.accept_10_1_4_7_1_374 21 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 84 247 (accept_3_3 20 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  84 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 84 247 (Polychromatic418967fa.accept_24_18_12_7_1_14861 18 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 247 (accept_3_3 17 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 84 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 84 247 (accept_3_3 14 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  84 247 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 84 247 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 247 (accept_3_3 11 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 84 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 247
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 84 247 (accept_3_3 8 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84
  247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 84 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 84 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 247 (accept_3_3 5 84 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 84 247 (Polychromatic418967fa.accept_22_4_18_5_1_5358 4 84 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  84 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 247 (accept_3_3 2 84 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 247 (allA_of_3_1
  83 83 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 247 (allA_succ_of_accept 81 82 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 247 (accept_3_3 80 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 247 (accept_3_3 77 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 247 (accept_3_3 74 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 247 (Polychromatic418967fa.accept_17_4_14_9_1_5105 72 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 247 (accept_3_3 71 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 82 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 247 (accept_3_3 68 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 247 (accept_3_3 65 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 64 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 247 (accept_3_3 62 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 247 (accept_3_3 59 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 247 (Polychromatic418967fa.accept_18_4_10_13_1_5883 58 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 247 (accept_3_3 56 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 247 (Polychromatic418967fa.accept_10_5_2_7_1_345 55 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 247 (accept_3_3 53 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 247 (accept_3_3 50 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 247 (accept_3_3 47 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 247 (accept_3_3 44 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 247 (accept_3_3 41 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 247 (accept_3_3 38 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 247 (Polychromatic418967fa.accept_22_14_16_5_1_11815 36 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 247 (accept_3_3 35 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 82 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 247 (accept_3_3 32 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 247 (accept_3_3 29 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 247 (accept_3_3 26 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 247 (accept_3_3 23 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 247 (Polychromatic418967fa.accept_17_5_14_9_1_5104 22 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 247 (accept_3_3 20 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 247 (accept_3_3 17 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 247 (accept_3_3 14 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 247 (accept_3_3 11 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 82 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 247 (accept_3_3 8 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 82 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 247 (accept_3_3 5 82 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 82 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 247 (accept_3_3 2 82 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 247
  (allA_succ_of_accept 80 81 247 (accept_3_3 80 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 247 (Polychromatic418967fa.accept_25_4_6_22_1_14860 79 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 247 (accept_3_3 77 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 247 (accept_3_3 74 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 247 (Polychromatic418967fa.accept_15_13_6_7_1_1369 73 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 247 (Polychromatic418967fa.accept_14_2_11_9_1_2925 72 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 247 (accept_3_3 71 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 247 (accept_3_3 68 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 247 (Polychromatic418967fa.accept_17_16_13_9_1_11391 67 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 247 (accept_3_3 65 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 247 (accept_3_3 62 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 247 (Polychromatic418967fa.accept_18_6_9_13_1_3320 60 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 247 (accept_3_3 59 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 247
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 57 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 247 (accept_3_3 56 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 247 (accept_3_3 53 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 247 (accept_3_3 50 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 247 (Polychromatic418967fa.accept_23_3_12_17_1_14859 49 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 247 (accept_3_3 47 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 247
  (Polychromatic418967fa.accept_21_3_18_16_1_7331 45 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 247 (accept_3_3 44 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 247 (Polychromatic418967fa.accept_11_10_4_5_1_359 43 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 247 (accept_3_3 41 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 247 (accept_3_3 38 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 247 (Polychromatic418967fa.accept_25_12_6_22_1_14858 37 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 247 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 247 (accept_3_3 35 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 247 (accept_3_3 32 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 247 (Polychromatic418967fa.accept_15_1_6_7_1_6282 31 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 247 (accept_3_3 29 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 247 (accept_3_3 26 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 247 (Polychromatic418967fa.accept_22_3_15_5_1_13486 25 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 247 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 247 (accept_3_3 23 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 247
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 247 (accept_3_3 20 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 247 (accept_3_3 17 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 247 (accept_3_3 14 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 247 (accept_3_3 11 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 247
  (Polychromatic418967fa.accept_22_9_15_5_1_10413 9 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 247 (accept_3_3 8 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  247 (Polychromatic418967fa.accept_23_7_12_17_1_14857 7 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 247 (accept_3_3 5 81 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 247 (accept_3_3 2 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  247 (Polychromatic418967fa.accept_15_1_6_7_1_6282 1 81 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 247 (allA_of_3_1 80 80 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 247
  (allA_succ_of_accept 78 79 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 79 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 247 (accept_3_3 77 79 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 247 (Polychromatic418967fa.accept_17_8_11_9_1_5099 76 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 75 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 79 247 (accept_3_3 74 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  79 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 79 247 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 247 (accept_3_3 71 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 79 247 (Polychromatic418967fa.accept_15_10_4_7_1_3127 70 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 79 247 (accept_3_3 68 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  79 247 (Polychromatic418967fa.accept_16_3_15_7_1_3417 67 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 79 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 247 (accept_3_3 65 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 79 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 247
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 247 (accept_3_3 62 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 247 (Polychromatic418967fa.accept_26_9_1_13_1_9498 61 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 247 (accept_3_3 59 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 247 (Polychromatic418967fa.accept_10_8_9_7_1_1118 58 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 57 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 247 (accept_3_3 56 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 247 (Polychromatic418967fa.accept_16_6_15_7_1_1510 54 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 247 (accept_3_3 53 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 247 (Polychromatic418967fa.accept_10_2_9_7_1_720 52 79 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 247 (accept_3_3 50 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 247 (Polychromatic418967fa.accept_23_3_10_17_1_14856 49 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 247 (accept_3_3 47 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 247
  (Polychromatic418967fa.accept_25_20_4_22_1_14855 45 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 79 247 (accept_3_3 44 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 79 247 (Polychromatic418967fa.accept_16_11_15_7_1_5654 43 79 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 79 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 247 (accept_3_3 41 79 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 247 (Polychromatic418967fa.accept_15_10_4_7_1_3127
  40 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 247 (accept_3_3 38 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 247 (Polychromatic418967fa.accept_17_2_11_9_1_1739 36 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 247 (accept_3_3 35 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 247 (Polychromatic418967fa.accept_23_11_10_17_1_14854 34 79
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 247 (accept_3_3 32 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 247 (Polychromatic418967fa.accept_25_6_4_22_1_14853 31 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 247 (accept_3_3 29 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 247
  (Polychromatic418967fa.accept_15_12_4_7_1_3097 27 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 247 (accept_3_3 26 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 247 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 247 (accept_3_3 23 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 247 (Polychromatic418967fa.accept_10_2_9_7_1_720 22 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 247 (accept_3_3 20 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 247 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 247 (accept_3_3 17 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 247 (Polychromatic418967fa.accept_23_16_10_17_1_14852 16 79 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 247 (accept_3_3 14 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 247 (Polychromatic418967fa.accept_27_13_25_4_1_14851 13 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 247 (accept_3_3 11 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 247
  (Polychromatic418967fa.accept_25_9_4_22_1_13219 9 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 247 (accept_3_3 8 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  247 (Polychromatic418967fa.accept_23_7_10_17_1_14850 7 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 247 (accept_3_3 5 79 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 247 (Polychromatic418967fa.accept_18_4_7_13_1_3303 4 79 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 247 (accept_3_3 2 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  247 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 79 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 247
  (allA_succ_of_accept 77 78 247 (accept_3_3 77 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 247 (accept_3_3 74 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 247
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 247 (accept_3_3 71 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 247 (accept_3_3 68 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 247 (Polychromatic418967fa.accept_17_16_10_9_1_11361 67 78 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 66 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 78 247 13 5 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 78 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 78 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 78 247 (Polychromatic418967fa.accept_16_15_14_7_1_10555 63 78
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 247 (accept_3_3 62 78 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 247
  (Polychromatic418967fa.accept_21_18_15_16_1_2917 60 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 78 247 (accept_3_3 59 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 247 (Polychromatic418967fa.accept_16_10_14_7_1_2372 58 78 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 78 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 247 (accept_3_3 56 78 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 55
  78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 247
  (Polychromatic418967fa.accept_17_3_10_9_1_8970 54 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 247 (accept_3_3 53 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78
  247 13 4 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  78 247 (Polychromatic418967fa.accept_20_11_18_7_1_1100 51 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 247 (accept_3_3 50 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 78 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 78 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 247 (accept_3_3 47 78 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 46
  78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 78 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 78 247 (accept_3_3 44 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  78 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 78 247 (Polychromatic418967fa.accept_15_12_3_7_1_4123 42 78 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 247 (accept_3_3 41 78 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 247 (Polychromatic418967fa.accept_15_10_3_7_1_715 40 78 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 247 13 3 6 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 247 (accept_3_3 38 78 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 247
  (Polychromatic418967fa.accept_16_4_14_7_1_5641 36 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 247 (accept_3_3 35 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 247 (accept_3_3 32 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 78 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 247 (accept_3_3 29 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 247 13 2 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 247 (accept_3_3 23 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 247 (Polychromatic418967fa.accept_20_2_18_7_1_3394 22 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 247 (accept_3_3 20 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 78 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 247
  (Polychromatic418967fa.accept_17_1_10_9_1_3884 18 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 247 (accept_3_3 17 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 247 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 247 (accept_3_3 14 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 13 78 247 13 1 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 12 78 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 78 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 247 (accept_3_3 11 78 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 78 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 78 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 247 (accept_3_3 8 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78
  247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 78 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 78 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 247 (accept_3_3 5 78 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 78 247 (Polychromatic418967fa.accept_15_4_3_7_1_713 4 78 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  78 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 247 (accept_3_3 2 78 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 247 (allA_of_3_1 77 77
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 247 (allA_succ_of_accept 75 76 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 247 (accept_3_3 74 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 247 (Polychromatic418967fa.accept_11_6_10_5_1_341 72 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 247 (accept_3_3 71 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 247 (Polychromatic418967fa.accept_11_4_10_5_1_1202 70 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 247 (accept_3_3 68 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 247 (accept_3_3 65 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 247 (accept_3_3 62 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 247 (Polychromatic418967fa.accept_10_1_6_7_1_710 61 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 247 (accept_3_3 59 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 76 247 19 3 4 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 76 247 (accept_3_3 56 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 55 76
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 247
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 54 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 247 (accept_3_3 53 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 247 (accept_3_3 50 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 247 (Polychromatic418967fa.accept_20_9_16_7_1_1129 49 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 247
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 247 (accept_3_3 47 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 247 (accept_3_3 44 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 247
  (Polychromatic418967fa.accept_28_14_20_23_1_14849 42 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 76 247 (accept_3_3 41 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 76 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 40 76 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 247 19 2 4 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 247
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 76 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 76 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 247 (accept_3_3 35 76 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 76 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 247 (accept_3_3 32 76
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 247 (Polychromatic418967fa.accept_7_3_6_2_1_90
  31 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 247
  (Polychromatic418967fa.accept_21_9_13_16_1_2914 30 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 247 (accept_3_3 29 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 247 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 247 (accept_3_3 26 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 247 (accept_3_3 23 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 247 (accept_3_3 20 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 19 76 247 19 1 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 18 76 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 247 (accept_3_3 17 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 247 (Polychromatic418967fa.accept_17_16_8_9_1_1772 16 76
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 247 (accept_3_3 14 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 247 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 247 (Polychromatic418967fa.accept_23_12_7_17_1_14848 12 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 247 (accept_3_3 11 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 76 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 247 (accept_3_3 8 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  247 (Polychromatic418967fa.accept_18_7_4_13_1_3315 7 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 76 247 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 247 (accept_3_3 5 76 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 76 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 76 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 76 247 (accept_3_3 2 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76
  247 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 76 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 247
  (allA_succ_of_accept 74 75 247 (accept_3_3 74 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  75 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 73 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 75 247 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 247 (accept_3_3 71 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 247 (accept_3_3 68 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  75 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 247 (accept_3_3 65 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 247
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 75 247 (accept_3_3 62 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  75 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 75 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 247 (accept_3_3 59 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 247 (accept_3_3 56 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  75 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 75 247 (Polychromatic418967fa.accept_22_10_9_5_1_14847 54 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 247 (accept_3_3 53 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 75 247 (accept_3_3 50 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  75 247 (Polychromatic418967fa.accept_14_7_5_9_1_2911 49 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 75 247 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 247 (accept_3_3 47 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 247 (accept_3_3 44 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 247 (accept_3_3 41 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 247 (accept_3_3 38 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 247 (accept_3_3 35 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 247 (accept_3_3 32 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 247 (Polychromatic418967fa.accept_18_12_3_13_1_4494 30 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 247 (accept_3_3 29 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 247
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 27 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 247 (accept_3_3 26 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 247 (accept_3_3 23 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 247 (accept_3_3 20 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 247 (accept_3_3 17 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 247 (accept_3_3 14 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 247 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 247 (accept_3_3 11 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 75 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 247 (accept_3_3 8 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 75 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 75 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 247 (accept_3_3 5 75 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 247 (accept_3_3 2 75 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 75
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 247 (allA_of_3_1 74 74
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 247 (allA_succ_of_accept 72 73 247
  (Polychromatic418967fa.accept_16_8_9_7_1_768 72 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 247 (accept_3_3 71 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 247 (accept_3_3 68 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 247 (Polychromatic418967fa.accept_16_3_9_7_1_6842 67 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 247 (accept_3_3 65 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 247 (Polychromatic418967fa.accept_17_12_5_9_1_6372 63 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 247 (accept_3_3 62 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 73 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 247 (accept_3_3 59 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 247 (accept_3_3 56 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 247 (accept_3_3 53 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 247 (accept_3_3 50 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 247 (Polychromatic418967fa.accept_21_7_10_16_1_4338 49 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 247 (accept_3_3 47 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 247 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 247 (accept_3_3 44 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 247 (accept_3_3 41 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 247 (accept_3_3 38 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 247 (Polychromatic418967fa.accept_23_14_4_17_1_13322 37 73 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 247 (accept_3_3 35 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 247 (accept_3_3 32 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 247 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 247 (accept_3_3 29 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 247 (Polychromatic418967fa.accept_18_10_1_13_1_2192 28 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 247 (accept_3_3 26 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 247 (accept_3_3 23 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 247 (accept_3_3 20 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 247 (accept_3_3 17 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 247 (accept_3_3 14 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 247 (accept_3_3 11 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 247 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 247 (accept_3_3 8 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 247 (accept_3_3 5 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  247 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 73 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 247 (accept_3_3 2 73 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 73 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 247 (allA_succ_of_accept 71
  72 247 (accept_3_3 71 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 247
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 70 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 69 72 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 247 (accept_3_3 68 72 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 247 (Polychromatic418967fa.accept_11_1_6_5_1_1732 67 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 247 (Polychromatic418967fa.accept_15_6_12_7_1_1360
  66 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 247 (accept_3_3 65
  72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 247
  (Polychromatic418967fa.accept_10_4_2_7_1_373 64 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 72 247 (Polychromatic418967fa.accept_14_7_2_9_1_2093 63 72 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 247 (accept_3_3 62 72 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 72 247 (Polychromatic418967fa.accept_27_7_18_4_1_14846 61 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 247
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 60 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 247 (accept_3_3 59 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  72 247 (Polychromatic418967fa.accept_23_12_3_17_1_14845 58 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 247 (Polychromatic418967fa.accept_16_9_8_7_1_4529 57 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 247 (accept_3_3 56 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 247 (Polychromatic418967fa.accept_10_5_2_7_1_345 55 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 247
  (Polychromatic418967fa.accept_10_4_2_7_1_373 54 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 72 247 (accept_3_3 53 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  72 247 (Polychromatic418967fa.accept_16_4_8_7_1_3396 52 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 247 (Polychromatic418967fa.accept_15_6_12_7_1_1360 51 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 247 (accept_3_3 50 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 72 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 247
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 48 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 247 (accept_3_3 47 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 247 (Polychromatic418967fa.accept_14_4_2_9_1_2092 46 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 247 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 247 (accept_3_3 44 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 247 (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 247
  (Polychromatic418967fa.accept_20_2_12_7_1_4799 42 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 247 (accept_3_3 41 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 247 (Polychromatic418967fa.accept_15_10_12_7_1_1358 40 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 247 (accept_3_3 38 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 247 (Polychromatic418967fa.accept_20_17_12_7_1_4759 37 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 247
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 247 (accept_3_3 35 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 247 (Polychromatic418967fa.accept_15_3_12_7_1_1346 33 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 247 (accept_3_3 32 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 247 (Polychromatic418967fa.accept_16_15_8_7_1_3407 31 72
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 247
  (Polychromatic418967fa.accept_17_13_4_9_1_6390 30 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 247 (accept_3_3 29 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 247 (Polychromatic418967fa.accept_16_12_8_7_1_4530 28 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 247 (Polychromatic418967fa.accept_21_6_9_16_1_2939 27 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 247 (accept_3_3 26 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 247 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 72 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 247
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 247 (accept_3_3 23 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 247 (Polychromatic418967fa.accept_20_2_12_7_1_4799 22 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 247 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 247 (accept_3_3 20 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 72 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 247
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 247 (accept_3_3 17 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 247 (Polychromatic418967fa.accept_32_16_8_23_1_14844 16 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 247 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 247 (accept_3_3 14 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 247 (Polychromatic418967fa.accept_17_13_4_9_1_6390 13 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 247
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 247 (accept_3_3 11 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 247 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 247 (accept_3_3 8 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 247 (Polychromatic418967fa.accept_14_7_2_9_1_2093 7 72 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 247
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 6 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 247 (accept_3_3 5 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  247 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 72 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 72 247 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 72 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 247 (accept_3_3 2 72 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 72 247 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 72 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 247 (allA_of_3_1 71 71 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 247 (allA_succ_of_accept 69 70 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 247 (accept_3_3 68 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 247 (Polychromatic418967fa.accept_21_4_7_16_1_2938 67 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 247 (accept_3_3 65 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 247 (accept_3_3 62 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 247 (accept_3_3 59 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 247 (Polychromatic418967fa.accept_17_7_2_9_1_6396 58 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 247 (accept_3_3 56 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 247 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 247 (accept_3_3 53 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 247 (accept_3_3 50 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 247 (accept_3_3 47 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 247 (accept_3_3 44 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 247 (Polychromatic418967fa.accept_11_10_4_5_1_359 43 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 247 (accept_3_3 41 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 247 (accept_3_3 38 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 247 (Polychromatic418967fa.accept_25_11_20_22_1_14843 36 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 247 (accept_3_3 35 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 34 70
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 247 (accept_3_3 32 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 31 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 247 (accept_3_3 29 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 247 (accept_3_3 26 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 247 (accept_3_3 23 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 247 (Polychromatic418967fa.accept_21_1_7_16_1_5859 22 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 247 (accept_3_3 20 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 247 (Polychromatic418967fa.accept_15_3_10_7_1_2196 18 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 247 (accept_3_3 17 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 70 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 247 (accept_3_3 14 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 247 (accept_3_3 11 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 247 (accept_3_3 8 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  247 (Polychromatic418967fa.accept_17_7_2_9_1_6396 7 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 70 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 247 (accept_3_3 5 70 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 70 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 247 (accept_3_3 2 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 247
  (allA_succ_of_accept 68 69 247 (accept_3_3 68 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 247 (accept_3_3 65 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 247
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 247 (accept_3_3 62 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 247 (accept_3_3 59 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 247 (accept_3_3 56 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 247 (accept_3_3 53 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 247 (accept_3_3 50 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 247 (Polychromatic418967fa.accept_17_15_1_9_1_10058 49 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 247 (accept_3_3 47 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 247 (accept_3_3 44 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 247 (accept_3_3 41 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 247 (accept_3_3 38 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 247 (accept_3_3 35 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 247
  (Polychromatic418967fa.accept_21_12_6_16_1_5855 33 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 247 (accept_3_3 32 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 247 (accept_3_3 29 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 247
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 247 (accept_3_3 26 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 247 (accept_3_3 23 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 247 (accept_3_3 20 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 247 (accept_3_3 17 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 247 (accept_3_3 14 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 247 (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 247 (accept_3_3 11 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 247
  (Polychromatic418967fa.accept_21_9_6_16_1_5857 9 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 247 (accept_3_3 8 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 69 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 247 (accept_3_3 5 69 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 69
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 247 (accept_3_3 2 69 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 69
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 247 (allA_of_3_1 68 68 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 247 (allA_succ_of_accept 66 67 247
  (Polychromatic418967fa.accept_23_20_21_17_1_10029 66 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 67 247 (accept_3_3 65 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 67 247 (Polychromatic418967fa.accept_17_13_16_9_1_5128 64 67 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 247 (Polychromatic418967fa.accept_16_15_3_7_1_3389 63 67
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 247 (accept_3_3 62 67 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 61
  67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 247
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 247 (accept_3_3 59 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 247 (Polychromatic418967fa.accept_14_2_11_9_1_2925 58 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 247 (Polychromatic418967fa.accept_16_9_3_7_1_6883 57 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 247 (accept_3_3 56 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 247 (accept_3_3 53 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 247 (Polychromatic418967fa.accept_21_9_4_16_1_9022 51 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 247 (accept_3_3 50 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 247 (Polychromatic418967fa.accept_21_7_4_16_1_5888 49 67
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 247 (accept_3_3 47 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 247 (Polychromatic418967fa.accept_24_22_19_7_1_14842 46 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 247 (Polychromatic418967fa.accept_23_22_21_17_1_14839 45 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 247 (accept_3_3 44 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 247 (Polychromatic418967fa.accept_16_11_3_7_1_2375 43 67
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 247
  (Polychromatic418967fa.accept_16_10_3_7_1_8094 42 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 247 (accept_3_3 41 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 247 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 247 (accept_3_3 38 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 247 (Polychromatic418967fa.accept_22_15_1_5_1_14841 37 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 247
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 247 (accept_3_3 35 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 247 (accept_3_3 32 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 247 (Polychromatic418967fa.accept_16_15_3_7_1_3389 31 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 247
  (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 247 (accept_3_3 29 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 247 (accept_3_3 26 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 247 (Polychromatic418967fa.accept_16_9_3_7_1_6883 25 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 247
  (Polychromatic418967fa.accept_25_24_17_22_1_14840 24 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 67 247 (accept_3_3 23 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 67 247 (Polychromatic418967fa.accept_23_22_21_17_1_14839 22 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 247
  (Polychromatic418967fa.accept_22_21_1_5_1_13426 21 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 247 (accept_3_3 20 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 247 (Polychromatic418967fa.accept_22_18_1_5_1_14838 18 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 247 (accept_3_3 17 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 247 (Polychromatic418967fa.accept_14_2_11_9_1_2925 16 67
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 247
  (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 247 (accept_3_3 14 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 247 (accept_3_3 11 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 247 (Polychromatic418967fa.accept_16_10_3_7_1_8094 10 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 247
  (Polychromatic418967fa.accept_16_9_3_7_1_6883 9 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 247 (accept_3_3 8 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  247 (Polychromatic418967fa.accept_21_7_4_16_1_5888 7 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 67 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 247 (accept_3_3 5 67 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 67 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 247
  (Polychromatic418967fa.accept_22_3_1_5_1_13464 3 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 67 247 (accept_3_3 2 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67
  247 (Polychromatic418967fa.accept_24_1_19_7_1_6281 1 67 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 67 247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 247
  (allA_succ_of_accept 65 66 247 (accept_3_3 65 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  66 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 66 247 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 247 (accept_3_3 62 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 66 247 (accept_3_3 59 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  66 247 (Polychromatic418967fa.accept_15_13_6_7_1_1369 58 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 66 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 247 (accept_3_3 56 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 54 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 66 247 (accept_3_3 53 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  66 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 66 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 247 (accept_3_3 50 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 66 247 (accept_3_3 47 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  66 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 66 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 247 (accept_3_3 44 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 66 247 (accept_3_3 41 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  66 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 66 247 (Polychromatic418967fa.accept_18_3_12_13_1_3307 39 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 247 (accept_3_3 38 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 247 (accept_3_3 35 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  66 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 247 (accept_3_3 32 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 247 (Polychromatic418967fa.accept_10_1_6_7_1_710 31 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 247
  (Polychromatic418967fa.accept_21_9_3_16_1_1684 30 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 66 247 (accept_3_3 29 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  66 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 66 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 247 (accept_3_3 26 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 247 (accept_3_3 23 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  66 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 66 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 247 (accept_3_3 20 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 247
  (Polychromatic418967fa.accept_17_1_15_9_1_1743 18 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 247 (accept_3_3 17 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  66 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 247 (accept_3_3 14 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 66 247 (accept_3_3 11 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  66 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 66 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 247 (accept_3_3 8 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 247 (accept_3_3 5 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  247 (Polychromatic418967fa.accept_26_4_14_13_1_14817 4 66 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 66 247 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 247 (accept_3_3 2 66 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 247 (allA_of_3_1 65 65 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 247 (allA_succ_of_accept 63 64 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 247 (accept_3_3 62 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 247 (accept_3_3 59 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 64 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 247 (accept_3_3 56 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 247 (Polychromatic418967fa.accept_29_25_6_15_1_14837 54 64 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 247 (accept_3_3 53 64 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 64 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 247 (accept_3_3 50 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 247 (Polychromatic418967fa.accept_21_7_1_16_1_9032 49 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 247 (accept_3_3 47 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 64 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 247 (accept_3_3 44 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 247 (accept_3_3 41 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 247 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 64 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 247 (accept_3_3 38 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 247 (Polychromatic418967fa.accept_18_1_10_13_1_500 37 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 247 (Polychromatic418967fa.accept_21_15_1_16_1_2930 36 64 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 247 (accept_3_3 35 64 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 64 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 247 (accept_3_3 32 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 247 (accept_3_3 29 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 247 (Polychromatic418967fa.accept_21_7_1_16_1_9032 28 64 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 247 (accept_3_3 26 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 247 (accept_3_3 23 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 247 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 64 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 247 (accept_3_3 20 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 247 (Polychromatic418967fa.accept_18_1_10_13_1_500 19 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 247 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 247 (accept_3_3 17 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 64 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 247 (accept_3_3 14 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 247 (accept_3_3 11 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 64 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 247 (accept_3_3 8 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 64 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 247 (accept_3_3 5 64 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 247 (Polychromatic418967fa.accept_17_4_13_9_1_921 4 64 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 247 (accept_3_3 2 64 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 247 (Polychromatic418967fa.accept_10_1_4_7_1_374 1
  64 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 247 (allA_succ_of_accept 62 63 247
  (accept_3_3 62 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 247
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 61 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 247 (Polychromatic418967fa.accept_18_6_9_13_1_3320 60 63 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 247 (accept_3_3 59 63 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 247 (Polychromatic418967fa.accept_11_2_8_5_1_1219
  57 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 247 (accept_3_3 56
  63 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 247
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 247 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 63 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 247 (accept_3_3 53 63 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 63 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 247 (Polychromatic418967fa.accept_16_3_15_7_1_3417
  51 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 247 (accept_3_3 50
  63 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 247
  (Polychromatic418967fa.accept_15_4_3_7_1_713 49 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 63 247 (Polychromatic418967fa.accept_17_14_12_9_1_2774 48 63 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 247 (accept_3_3 47 63 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 63 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 247 (Polychromatic418967fa.accept_10_5_3_7_1_1108
  45 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 247 (accept_3_3 44
  63 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 247
  (Polychromatic418967fa.accept_16_11_15_7_1_5654 43 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 63 247 (Polychromatic418967fa.accept_15_12_3_7_1_4123 42 63 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 247 (accept_3_3 41 63 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 63 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 247
  (Polychromatic418967fa.accept_17_5_12_9_1_10091 39 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 247 (accept_3_3 38 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 247 (Polychromatic418967fa.accept_24_13_15_7_1_13263 37 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 247 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 247 (accept_3_3 35 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 247 (accept_3_3 32 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 247 (Polychromatic418967fa.accept_17_14_12_9_1_2774 31 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 247 (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 247 (accept_3_3 29 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 247
  (Polychromatic418967fa.accept_15_12_3_7_1_4123 27 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 247 (accept_3_3 26 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 247 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 247 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 247 (accept_3_3 23 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 63 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 247 (accept_3_3 20 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 247 (Polychromatic418967fa.accept_14_5_7_9_1_3828 19 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 247 (Polychromatic418967fa.accept_24_18_15_7_1_14836 18 63 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 247 (accept_3_3 17 63 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 247
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 247 (accept_3_3 14 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 247 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 247 (Polychromatic418967fa.accept_14_12_7_9_1_726 12 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 247 (accept_3_3 11 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 63 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 247 (accept_3_3 8 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  247 (Polychromatic418967fa.accept_26_7_11_13_1_14835 7 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 247 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 247 (accept_3_3 5 63 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 247
  (Polychromatic418967fa.accept_11_3_8_5_1_336 3 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 247 (accept_3_3 2 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  247 (Polychromatic418967fa.accept_28_1_7_23_1_14834 1 63 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 247))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 247
  (allA_of_3_1 62 62 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 247 (allA_succ_of_accept 60 61 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 247 (accept_3_3 59 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 247 (accept_3_3 56 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 61 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 247 (accept_3_3 53 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 247 (accept_3_3 50 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 247 (Polychromatic418967fa.accept_14_7_5_9_1_2911 49 61 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 247 (accept_3_3 47 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 247 (accept_3_3 44 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 247 (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 61 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 247 (accept_3_3 41 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 40 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 247 (accept_3_3 38 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 61 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 247
  (Polychromatic418967fa.accept_10_6_1_7_1_342 36 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 247 (accept_3_3 35 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 247 (accept_3_3 32 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 61 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 247 (accept_3_3 29 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 247 (Polychromatic418967fa.accept_25_2_11_22_1_14833 27 61 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 247 (accept_3_3 26 61 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 61 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 247 (accept_3_3 23 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 247 (accept_3_3 20 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 247 (accept_3_3 17 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 247 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 247 (accept_3_3 14 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 247 (Polychromatic418967fa.accept_17_13_10_9_1_946 13 61 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 247 (accept_3_3 11 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 247 (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 247 (accept_3_3 8 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 247 (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 61 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 247 (accept_3_3 5 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  247 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 61 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 61 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 247 (accept_3_3 2 61 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 61 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 247 (allA_succ_of_accept 59 60 247 (accept_3_3 59 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 247 (Polychromatic418967fa.accept_14_2_4_9_1_2121 58 60 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 60 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 247 (accept_3_3 56 60 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 55
  60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 247 (accept_3_3 53 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 247 (accept_3_3 50 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 247 (Polychromatic418967fa.accept_23_3_14_17_1_14832 49 60 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 247 (accept_3_3 47 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 247 (Polychromatic418967fa.accept_18_9_6_13_1_4499 45 60 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 247 (accept_3_3 44 60 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 60 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 247
  (Polychromatic418967fa.accept_22_20_16_5_1_8693 42 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 247 (accept_3_3 41 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  60 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 247 (accept_3_3 38 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 60 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 247
  (Polychromatic418967fa.accept_16_4_12_7_1_4475 36 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 247 (accept_3_3 35 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 247 (accept_3_3 32 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 247 (Polychromatic418967fa.accept_22_9_16_5_1_14831 31 60 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 247 (accept_3_3 29 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 247 (accept_3_3 26 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 60 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 247
  (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 247 (accept_3_3 23 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 247 (Polychromatic418967fa.accept_27_22_6_4_1_7186 22 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 247 (accept_3_3 20 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 60 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 247
  (Polychromatic418967fa.accept_16_2_12_7_1_3410 18 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 247 (accept_3_3 17 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 247 (Polychromatic418967fa.accept_21_15_18_16_1_2942 15 60 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 247 (accept_3_3 14 60 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 60 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 247 (accept_3_3 11 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 247 (Polychromatic418967fa.accept_18_9_6_13_1_4499 9 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 247 (accept_3_3 8 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 247 (accept_3_3 5 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  247 (Polychromatic418967fa.accept_16_4_12_7_1_4475 4 60 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 60 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 247 (accept_3_3 2 60 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 60 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 247 (allA_of_3_1 59 59 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 247 (allA_succ_of_accept 57 58 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 247 (accept_3_3 56 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 247 (Polychromatic418967fa.accept_10_5_8_7_1_2174 55 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 247 (Polychromatic418967fa.accept_15_9_13_7_1_1361 54 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 247 (accept_3_3 53 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 247 (Polychromatic418967fa.accept_11_8_3_5_1_355 52 58 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 247 (accept_3_3 50 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 247 (Polychromatic418967fa.accept_25_23_8_22_1_14830 48 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 247 (accept_3_3 47 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 247 (Polychromatic418967fa.accept_14_4_2_9_1_2092 46 58 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 247 (accept_3_3 44 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 247 (Polychromatic418967fa.accept_18_7_4_13_1_3315 43 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 247 (Polychromatic418967fa.accept_20_2_18_7_1_3394 42 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 247 (accept_3_3 41 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 58 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 247 (accept_3_3 38 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 247 (Polychromatic418967fa.accept_15_6_13_7_1_222 36 58 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 247 (accept_3_3 35 58 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 247 (Polychromatic418967fa.accept_25_9_8_22_1_14829 34 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 247 (accept_3_3 32 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 247 (Polychromatic418967fa.accept_20_11_18_7_1_1100 31 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 247 (Polychromatic418967fa.accept_11_8_3_5_1_355 30 58 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 247 (accept_3_3 29 58 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 247 (accept_3_3 26 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 247 (Polychromatic418967fa.accept_15_9_13_7_1_1361 24 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 247 (accept_3_3 23 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 247 (Polychromatic418967fa.accept_17_5_7_9_1_5122 22 58 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 247 (accept_3_3 20 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 247 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 247 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 58 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 247 (accept_3_3 17 58 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 247 (accept_3_3 14 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 247 (Polychromatic418967fa.accept_25_12_8_22_1_14828 12 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 247 (accept_3_3 11 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 247 (Polychromatic418967fa.accept_18_10_4_13_1_3296 10 58
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 247 (accept_3_3 8 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  247 (Polychromatic418967fa.accept_14_7_2_9_1_2093 7 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 58 247 (Polychromatic418967fa.accept_15_6_13_7_1_222 6 58 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 247 (accept_3_3 5 58 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 58 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 58 247 (accept_3_3 2 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58
  247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 247 (allA_succ_of_accept 56
  57 247 (accept_3_3 56 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 247 (accept_3_3 53 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 51
  57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 247 (accept_3_3 50 57
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 247
  (Polychromatic418967fa.accept_15_4_12_7_1_3115 49 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 247 (accept_3_3 47 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 45
  57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 247 (accept_3_3 44 57
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 247
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 247 (accept_3_3 41 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 247 (Polychromatic418967fa.accept_12_3_9_7_1_472
  39 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 57 247 19 2 3 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 57 247
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 247 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 247 (accept_3_3 35 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 33
  57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 247 (accept_3_3 32 57
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 247 (accept_3_3 29 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 27
  57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 247 (accept_3_3 26 57
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 247
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 247 (accept_3_3 23 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 247 (Polychromatic418967fa.accept_15_6_12_7_1_1360
  21 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 247 (accept_3_3 20
  57 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19 57 247 19 1 3 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 18 57 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 247 (accept_3_3 17 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 57 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 247 (accept_3_3 14 57 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 57 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 247
  (Polychromatic418967fa.accept_18_12_3_13_1_4494 12 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 247 (accept_3_3 11 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 247 (Polychromatic418967fa.accept_18_9_3_13_1_5905 9 57 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 247 (accept_3_3 8 57 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 57 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 247 (accept_3_3 5 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 247 (accept_3_3 2 57 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 57 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 247 (allA_of_3_1 56 56 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 247
  (allA_succ_of_accept 54 55 247 (Polychromatic418967fa.accept_23_8_9_17_1_14827 54 55 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 247 (accept_3_3 53 55 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 51
  55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 247 (accept_3_3 50 55
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 247
  (Polychromatic418967fa.accept_15_4_10_7_1_1356 49 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 247 (accept_3_3 47 55 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 45
  55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 247 (accept_3_3 44 55
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 247 (Polychromatic418967fa.accept_7_1_6_2_1_18
  43 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 247 (accept_3_3 41 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 247 (Polychromatic418967fa.accept_21_19_13_16_1_7317 40 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 247 (accept_3_3 38 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 247 (Polychromatic418967fa.accept_22_15_11_5_1_13490 37 55 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 247 (accept_3_3 35 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 247 (accept_3_3 32 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 55 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 247 (accept_3_3 29 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 247 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 247 (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 55 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 247 (accept_3_3 26 55 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 55 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 247 (accept_3_3 23 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 247 (accept_3_3 20 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 55 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 247 (accept_3_3 17 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 247 (accept_3_3 14 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 247 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 55 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 247 (accept_3_3 11 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 247 (Polychromatic418967fa.accept_21_9_13_16_1_2914 9 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 247 (accept_3_3 8 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 247 (accept_3_3 5 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  247 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 55 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 55 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 247 (accept_3_3 2 55 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 55 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 247)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 247 (allA_succ_of_accept 53 54 247 (accept_3_3 53 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 54 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 54 247 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 54 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 247 (accept_3_3 50 54 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 247
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 247 (accept_3_3 47 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 247 (accept_3_3 44 54 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 247 (Polychromatic418967fa.accept_10_3_4_7_1_353 43 54 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 247
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 247 (accept_3_3 41 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 247 (Polychromatic418967fa.accept_17_6_3_9_1_7739 40 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 54 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 247 (accept_3_3 38 54 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 247
  (Polychromatic418967fa.accept_24_12_6_7_1_13305 36 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 247 (accept_3_3 35 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 247 (Polychromatic418967fa.accept_25_9_4_22_1_13219 34 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 247 (accept_3_3 32 54 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 54 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 247
  (Polychromatic418967fa.accept_21_9_12_16_1_13518 30 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 54 247 (accept_3_3 29 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 247 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 54 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 247 (Polychromatic418967fa.accept_17_10_3_9_1_14826 27 54
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 247 (accept_3_3 26 54 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 247 (accept_3_3 23 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 247 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 247 (accept_3_3 20 54 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 247 (Polychromatic418967fa.accept_22_19_10_5_1_8698 19 54 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 247 (accept_3_3 17 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 247 (Polychromatic418967fa.accept_15_1_9_7_1_3130 16 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 247 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 54 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 247 (accept_3_3 14 54 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 247
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 247 (accept_3_3 11 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 247 (accept_3_3 8 54 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 247 (Polychromatic418967fa.accept_14_7_12_9_1_2926 7 54 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 247
  (Polychromatic418967fa.accept_11_6_10_5_1_341 6 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 247 (accept_3_3 5 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  247 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 54 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 54 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 247 (accept_3_3 2 54 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 54 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 247))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 247 (allA_of_3_1 53 53 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 247
  (allA_succ_of_accept 51 52 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 247 (accept_3_3 50 52 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 52 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 48
  52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 247 (accept_3_3 47 52
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 247 (Polychromatic418967fa.accept_9_1_7_4_1_52
  46 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 52 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 52 247 (accept_3_3 44 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  52 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 52 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 52 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 247 (accept_3_3 41 52 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 52 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 52 247 13 3 4 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 52 247 (accept_3_3 38 52 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 52 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 247 (accept_3_3 35 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 247 (accept_3_3 32 52 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 247 (Polychromatic418967fa.accept_25_6_2_22_1_14825 31 52 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 247 (accept_3_3 29 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 247 13 2 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 247 (Polychromatic418967fa.accept_10_5_2_7_1_345 25
  52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 247 (accept_3_3 23 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 247 (accept_3_3 20 52 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 52 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 247
  (Polychromatic418967fa.accept_25_18_2_22_1_14824 18 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 52 247 (accept_3_3 17 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 52 247 (Polychromatic418967fa.accept_23_16_6_17_1_14823 16 52 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 247 (accept_3_3 14 52 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 52 247 13 1 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 52 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 12
  52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 247 (accept_3_3 11 52
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 247 (Polychromatic418967fa.accept_9_1_7_4_1_52
  10 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 247 (accept_3_3 8 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  247 (Polychromatic418967fa.accept_21_7_10_16_1_4338 7 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 52 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 52 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 247 (accept_3_3 5 52 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 52 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 52 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 52 247 (accept_3_3 2 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52
  247 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 52 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 247)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 247 (allA_succ_of_accept 50 51 247
  (accept_3_3 50 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 247
  (Polychromatic418967fa.accept_21_7_9_16_1_9027 49 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 51 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 247 (accept_3_3 47 51 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 51 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 247 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 247 (accept_3_3 44
  51 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 247
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 247 (Polychromatic418967fa.accept_11_9_7_5_1_749 42 51 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 247 (accept_3_3 41 51 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 39
  51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 247 (accept_3_3 38 51
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 247 (Polychromatic418967fa.accept_9_1_6_4_1_49
  37 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 247
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 247 (accept_3_3 35 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 247 (Polychromatic418967fa.accept_12_9_3_7_1_924 33 51 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 247 (accept_3_3 32 51 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 247 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 51 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 247 (accept_3_3 29 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 247 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 51 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 247 (accept_3_3 26 51 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 51 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 247
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 247 (accept_3_3 23 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 247 (accept_3_3 20 51 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 51 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 247
  (Polychromatic418967fa.accept_20_18_11_7_1_6344 18 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 247 (accept_3_3 17 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 247 (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 51 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 247 (accept_3_3 14 51 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 247 (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 51
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 247
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 247 (accept_3_3 11 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 247 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 51 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 247 (accept_3_3 8 51 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 51 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 247
  (Polychromatic418967fa.accept_10_6_1_7_1_342 6 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 247 (accept_3_3 5 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 51 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 247 (accept_3_3 2 51 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 51 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 247)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 247 (allA_of_3_1 50 50 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 247
  (allA_succ_of_accept 48 49 247 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 49 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 247 (accept_3_3 47 49 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 247 (Polychromatic418967fa.accept_20_5_9_7_1_10766
  45 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 247 (accept_3_3 44
  49 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 247
  (Polychromatic418967fa.accept_21_1_7_16_1_5859 43 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 247 (accept_3_3 41 49 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 247 (Polychromatic418967fa.accept_14_12_7_9_1_726 40 49 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 247
  (Polychromatic418967fa.accept_25_14_24_22_1_14822 39 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 49 247 (accept_3_3 38 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 49 247 (Polychromatic418967fa.accept_20_17_9_7_1_13576 37 49 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 247 (Polychromatic418967fa.accept_20_16_9_7_1_3402 36 49
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 247 (accept_3_3 35 49 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 247
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 247 (accept_3_3 32 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 247 (Polychromatic418967fa.accept_21_10_7_16_1_9036 31 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 247 (accept_3_3 29 49 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 247 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 49 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 247
  (Polychromatic418967fa.accept_15_12_4_7_1_3097 27 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 247 (accept_3_3 26 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 247 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 247 (Polychromatic418967fa.accept_16_8_1_7_1_2355 24 49 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 247 (accept_3_3 23 49 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 247
  (Polychromatic418967fa.accept_25_21_24_22_1_14821 21 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 49 247 (accept_3_3 20 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 49 247 (Polychromatic418967fa.accept_14_5_7_9_1_3828 19 49 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 247 (accept_3_3 17 49 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 247 (Polychromatic418967fa.accept_14_2_7_9_1_2937
  16 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 247
  (Polychromatic418967fa.accept_25_15_24_22_1_14820 15 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 49 247 (accept_3_3 14 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 49 247 (Polychromatic418967fa.accept_21_13_7_16_1_7351 13 49 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 247 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 49 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 247 (accept_3_3 11 49 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 247
  (Polychromatic418967fa.accept_21_9_7_16_1_5904 9 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 247 (accept_3_3 8 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  247 (Polychromatic418967fa.accept_17_7_15_9_1_9019 7 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 247 (accept_3_3 5 49 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 247 (Polychromatic418967fa.accept_21_4_7_16_1_2938 4 49 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 247
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 3 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 247 (accept_3_3 2 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  247 (Polychromatic418967fa.accept_17_1_15_9_1_1743 1 49 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 49 247))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 247 (allA_succ_of_accept
  47 48 247 (accept_3_3 47 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 46 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 48 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 247 (accept_3_3 44 48 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 48 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 42
  48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 247 (accept_3_3 41 48
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 247
  (Polychromatic418967fa.accept_15_10_3_7_1_715 40 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 48 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 247 (accept_3_3 38 48 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 48 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 48 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 36
  48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 247 (accept_3_3 35 48
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 247
  (Polychromatic418967fa.accept_9_7_3_4_1_218 34 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 247 (accept_3_3 32 48 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 48 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 48 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 247 (Polychromatic418967fa.accept_20_10_8_7_1_7834
  30 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 247 (accept_3_3 29
  48 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 247
  (Polychromatic418967fa.accept_9_1_3_4_1_47 28 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 48 247 (Polychromatic418967fa.accept_15_12_3_7_1_4123 27 48 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 247 (accept_3_3 26 48 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 48 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 48 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 24
  48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 247 (accept_3_3 23 48
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 247 (Polychromatic418967fa.accept_7_1_6_2_1_18
  22 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 247
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 48 247 (accept_3_3 20 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  48 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 48 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 48 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 247 (accept_3_3 17 48 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 48 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 48 247 (accept_3_3 14 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  48 247 (Polychromatic418967fa.accept_21_13_6_16_1_9023 13 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 48 247 (Polychromatic418967fa.accept_15_12_3_7_1_4123 12 48 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 247 (accept_3_3 11 48 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 48 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 48 247
  (Polychromatic418967fa.accept_10_9_8_7_1_714 9 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 48 247 (accept_3_3 8 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48
  247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 48 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 48 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 247 (accept_3_3 5 48 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 48 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 48 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 247 (accept_3_3 2 48 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 48
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  247)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 247 (allA_of_3_1 47 47 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 46 247 (allA_succ_of_accept 45 46 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 247 (accept_3_3 44 46 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 46 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 43
  46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 46 247 (accept_3_3 41 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  46 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 46 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 247 (accept_3_3 38 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 46 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 247
  (Polychromatic418967fa.accept_15_6_1_7_1_4079 36 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 46 247 (accept_3_3 35 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  46 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 46 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 247 (accept_3_3 32 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 46 247 (Polychromatic418967fa.accept_10_1_6_7_1_710 31 46 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 46 247 (accept_3_3 29 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  46 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 46 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 247 (accept_3_3 26 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 46 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 46 247 (accept_3_3 23 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  46 247 (Polychromatic418967fa.accept_17_5_12_9_1_10091 22 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 46 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 247 (accept_3_3 20 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 46 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 46 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 247
  (Polychromatic418967fa.accept_22_18_2_5_1_14819 18 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 46 247 (accept_3_3 17 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  46 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 46 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 247 (accept_3_3 14 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 46 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 46 247 (accept_3_3 11 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  46 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 10 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 46 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 247 (accept_3_3 8 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 46 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 46 247 (accept_3_3 5 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46
  247 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 46 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 46 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 247 (accept_3_3 2 46 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 247))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 45 247 (allA_succ_of_accept 44 45 247 (accept_3_3 44 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 45 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 247 (accept_3_3 41 45 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 40
  45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 247
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 247 (accept_3_3 38 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  45 247 (Polychromatic418967fa.accept_17_3_11_9_1_5100 37 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 247 (accept_3_3 35 45 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 247 (accept_3_3 32 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  45 247 (Polychromatic418967fa.accept_21_10_3_16_1_5909 31 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 45 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 247 (accept_3_3 29 45 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 247 (accept_3_3 26 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  45 247 (Polychromatic418967fa.accept_16_9_13_7_1_1509 25 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 247 (Polychromatic418967fa.accept_18_6_9_13_1_3320 24 45 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 247 (accept_3_3 23 45 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 247
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 21 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 247 (accept_3_3 20 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  45 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 247 (accept_3_3 17 45 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 247 (accept_3_3 14 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 247 (accept_3_3 11 45 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 247
  (Polychromatic418967fa.accept_16_9_13_7_1_1509 9 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 247 (accept_3_3 8 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  247 (Polychromatic418967fa.accept_21_7_3_16_1_7337 7 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 247 (accept_3_3 5 45 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 247
  (Polychromatic418967fa.accept_10_3_5_7_1_330 3 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 247 (accept_3_3 2 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45
  247 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 45 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 247))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 247 (allA_of_3_1 44 44 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 43 247 (allA_succ_of_accept 42 43 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 247 (accept_3_3 41 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 247 (Polychromatic418967fa.accept_18_4_7_13_1_3303 40 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 247 (accept_3_3 38 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 43 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 247
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 247 (accept_3_3 35 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 247 (accept_3_3 32 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 43 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 247 (accept_3_3 29 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 247 (accept_3_3 26 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 247 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 43 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 247 (accept_3_3 23 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 247 (Polychromatic418967fa.accept_14_8_1_9_1_2085 22 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 247 (accept_3_3 20 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 43 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 247
  (Polychromatic418967fa.accept_16_2_11_7_1_2352 18 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 247 (accept_3_3 17 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 247 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 247 (accept_3_3 14 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 43 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 247
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 247 (accept_3_3 11 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 247 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 247 (accept_3_3 8 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 247 (Polychromatic418967fa.accept_21_7_1_16_1_9032 7 43 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 247 (accept_3_3 5 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  247 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 43 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 43 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 247 (accept_3_3 2 43 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 247))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 247
  (allA_succ_of_accept 41 42 247 (accept_3_3 41 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 247 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 42 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 247 (accept_3_3 38 42 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 247
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 247 (accept_3_3 35 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 247 (accept_3_3 32 42 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 247 (Polychromatic418967fa.accept_28_3_14_23_1_14818 31 42 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 247 (accept_3_3 29 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 247 (Polychromatic418967fa.accept_18_9_6_13_1_4499 27 42 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 247 (accept_3_3 26 42 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 247
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 247 (accept_3_3 23 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 247 (Polychromatic418967fa.accept_26_22_16_13_1_9490 22 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 247 (accept_3_3 20 42 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 247
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 247 (accept_3_3 17 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 247 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 42 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 247 (accept_3_3 14 42 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 247 (accept_3_3 11 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 247 (accept_3_3 8 42 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 42 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 247
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 6 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 247 (accept_3_3 5 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  247 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 42 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 247 (accept_3_3 2 42 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 247)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 247
  (allA_of_3_1 41 41 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 247 (allA_succ_of_accept 39 40 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 247 (accept_3_3 38 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 247 (Polychromatic418967fa.accept_17_3_6_9_1_2761 37 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 247 (Polychromatic418967fa.accept_16_4_8_7_1_3396 36 40 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 247 (accept_3_3 35 40 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 40 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 247 (accept_3_3 32 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 247 (Polychromatic418967fa.accept_26_4_14_13_1_14817 30 40 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 247 (accept_3_3 29 40 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 247 (Polychromatic418967fa.accept_16_12_8_7_1_4530 28 40
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 247 (accept_3_3 26 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 40 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 247 (accept_3_3 23 40 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 40 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 247 (accept_3_3 20 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 40 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 247 (accept_3_3 17 40 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 40 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 247 (accept_3_3 14 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 247 (Polychromatic418967fa.accept_21_13_19_16_1_721 13 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 247 (Polychromatic418967fa.accept_15_12_10_7_1_1357 12 40 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 247 (accept_3_3 11 40 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 40 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 247 (accept_3_3 8 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  247 (Polychromatic418967fa.accept_14_7_12_9_1_2926 7 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 40 247 (Polychromatic418967fa.accept_25_6_15_22_1_14816 6 40 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 247 (accept_3_3 5 40 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 40 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 247 (accept_3_3 2 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 40 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 40 247)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 247 (allA_succ_of_accept 38 39 247
  (accept_3_3 38 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 247
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 247 (Polychromatic418967fa.accept_21_15_18_16_1_2942 36 39 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 247 (accept_3_3 35 39 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 39 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 33
  39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 247 (accept_3_3 32 39
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 247
  (Polychromatic418967fa.accept_15_1_9_7_1_3130 31 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 39 247 (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 39 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 247 (accept_3_3 29 39 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 39 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 27
  39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 39 247 13 2 3 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 247
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 247 (accept_3_3 23 39 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 247 (Polychromatic418967fa.accept_11_10_6_5_1_1239
  21 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 247 (accept_3_3 20
  39 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 39 247 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 39 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 247 (accept_3_3 17 39 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 39 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 15
  39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 247 (accept_3_3 14 39
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 39 247 13 1 3 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 39 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 247 (accept_3_3 11 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 247 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 39 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 247 (accept_3_3 8 39 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 39 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 247 (accept_3_3 5 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 247 (Polychromatic418967fa.accept_21_3_18_16_1_7331 3 39 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 247 (accept_3_3 2 39 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 39 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 247))))))))))))))))))))))))))))))))))))))) (allB_succ 38 247
  (allA_of_3_1 38 38 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 247 (allA_succ_of_accept 36 37 247
  (Polychromatic418967fa.accept_20_16_17_7_1_7845 36 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 247 (accept_3_3 35 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 37 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 247 (accept_3_3 32 37 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 247 (Polychromatic418967fa.accept_22_9_15_5_1_10413 31 37 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 247 (accept_3_3 29 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 247 (Polychromatic418967fa.accept_16_12_5_7_1_2360 28 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 247 (Polychromatic418967fa.accept_16_11_5_7_1_2395 27 37 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 247 (accept_3_3 26 37 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 37 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 247 (accept_3_3 23 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 37 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 247 (accept_3_3 20 37 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 247 (Polychromatic418967fa.accept_20_19_17_7_1_6299 19 37 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 247 (accept_3_3 17 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 37 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 247 (accept_3_3 14 37 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 247 (Polychromatic418967fa.accept_25_13_12_22_1_14815 13 37 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 247 (accept_3_3 11 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 247 (Polychromatic418967fa.accept_20_9_17_7_1_4748 9 37 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 247 (accept_3_3 8 37 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 247 (accept_3_3 5 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  247 (Polychromatic418967fa.accept_20_4_17_7_1_3393 4 37 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 37 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 37 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 247 (accept_3_3 2 37 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 247 (Polychromatic418967fa.accept_17_1_3_9_1_958 1 37 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 247))))))))))))))))))))))))))))))))))))) (allB_succ
  36 247 (allA_succ_of_accept 35 36 247 (accept_3_3 35 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 36 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 247 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 36 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 247 (accept_3_3 32 36 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 31
  36 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 247
  (Polychromatic418967fa.accept_11_8_3_5_1_355 30 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 247 (accept_3_3 29 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 247 (Polychromatic418967fa.accept_15_13_6_7_1_1369 28 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 247 (accept_3_3 26 36 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 247 (Polychromatic418967fa.accept_22_3_14_5_1_13382 25 36 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 247
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 247 (accept_3_3 23 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 247 (Polychromatic418967fa.accept_21_1_15_16_1_5891 22 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 247 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 36 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 247 (accept_3_3 20 36 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 36 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 247
  (Polychromatic418967fa.accept_21_18_15_16_1_2917 18 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 36 247 (accept_3_3 17 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 247 (Polychromatic418967fa.accept_15_1_6_7_1_6282 16 36 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 247 (Polychromatic418967fa.accept_14_1_8_9_1_1312 15 36 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 247 (accept_3_3 14 36 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  36 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 247
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 247 (accept_3_3 11 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 247 (Polychromatic418967fa.accept_20_9_16_7_1_1129 9 36 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 247 (accept_3_3 8 36 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 247 (Polychromatic418967fa.accept_17_7_2_9_1_6396 7 36 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 247 (accept_3_3 5 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  247 (Polychromatic418967fa.accept_17_4_2_9_1_3896 4 36 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 247 (accept_3_3 2 36 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 247 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 36 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 247)))))))))))))))))))))))))))))))))))) (allB_succ 35
  247 (allA_of_3_1 35 35 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 247 (allA_succ_of_accept 33 34 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 247 (accept_3_3 32 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 34 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 247 (accept_3_3 29 34 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 34 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 247 (accept_3_3 26 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 34 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 247 (accept_3_3 23 34 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 34 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 247 (accept_3_3 20 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 34 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 247 (accept_3_3 17 34 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 34 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 247 (accept_3_3 14 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 34 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 247 (accept_3_3 11 34 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 34 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 247 (accept_3_3 8 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  247 (Polychromatic418967fa.accept_21_7_13_16_1_9068 7 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 34 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 34 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 247 (accept_3_3 5 34 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 34 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 247 (accept_3_3 2 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34
  247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 247)))))))))))))))))))))))))))))))))) (allB_succ 33 247 (allA_succ_of_accept 32 33 247 (accept_3_3 32 33
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 247 (Polychromatic418967fa.accept_7_3_5_2_1_17
  31 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 247 (accept_3_3 29 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 247 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 33 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 247 (accept_3_3 26 33 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 33 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 247 (accept_3_3 23 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 247 (accept_3_3 20 33 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 33 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 247 (accept_3_3 17 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 247 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 33 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 247 (accept_3_3 14 33 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 247 (Polychromatic418967fa.accept_17_13_16_9_1_5128 13 33 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 247 (accept_3_3 11 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 247 (Polychromatic418967fa.accept_21_9_12_16_1_13518 9 33 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 247 (accept_3_3 8 33 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 33 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 247 (accept_3_3 5 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 33 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 247 (accept_3_3 2 33 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 33 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 247))))))))))))))))))))))))))))))))) (allB_succ 32 247
  (allA_of_3_1 32 32 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 247 (allA_succ_of_accept 30 31 247
  (Polychromatic418967fa.accept_16_14_15_7_1_5655 30 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 247 (accept_3_3 29 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 247 (Polychromatic418967fa.accept_21_7_10_16_1_4338 28 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 31 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 247 (accept_3_3 26 31 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 25 31 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 247
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 247 (accept_3_3 23 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 247 (Polychromatic418967fa.accept_15_6_1_7_1_4079 21 31 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 247 (accept_3_3 20 31 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 31 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 247
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 247 (accept_3_3 17 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 247 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 31 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 247 (accept_3_3 14 31 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 31 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 247
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 247 (accept_3_3 11 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 247 (Polychromatic418967fa.accept_15_10_1_7_1_5207 10 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 247 (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 31 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 247 (accept_3_3 8 31 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 247 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 31 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 247 (accept_3_3 5 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  247 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 31 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 247 (Polychromatic418967fa.accept_16_3_15_7_1_3417 3 31 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 247 (accept_3_3 2 31 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 31 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 247))))))))))))))))))))))))))))))) (allB_succ 30 247
  (allA_succ_of_accept 29 30 247 (accept_3_3 29 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 247 (Polychromatic418967fa.accept_17_10_13_9_1_3913 27 30 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 247 (accept_3_3 26 30 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 247 (accept_3_3 23 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 247 (Polychromatic418967fa.accept_17_5_13_9_1_9018 22 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 247 (accept_3_3 20 30 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 30 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 247
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 247 (accept_3_3 17 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 30 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 247 (accept_3_3 14 30 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 247
  (Polychromatic418967fa.accept_21_12_9_16_1_11973 12 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 30 247 (accept_3_3 11 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 30 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 247 (accept_3_3 8 30 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  30 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 247 (accept_3_3 5 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  247 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 30 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 30 247 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 30 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 247 (accept_3_3 2 30 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 247)))))))))))))))))))))))))))))) (allB_succ 29 247
  (allA_of_3_1 29 29 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 247 (allA_succ_of_accept 27 28 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 247 (accept_3_3 26 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 28 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 247 (accept_3_3 23 28 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 28 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 247 (accept_3_3 20 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 247 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 247 (Polychromatic418967fa.accept_16_2_12_7_1_3410 18 28 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 247 (accept_3_3 17 28 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 28 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 247 (accept_3_3 14 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 247 (Polychromatic418967fa.accept_21_13_7_16_1_7351 13 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 28 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 247 (accept_3_3 11 28 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 247 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 28 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 247 (accept_3_3 8 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 28 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 247 (accept_3_3 5 28 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 247 (Polychromatic418967fa.accept_16_4_12_7_1_4475 4 28 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 247 (accept_3_3 2 28 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 247 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1
  28 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 247))))))))))))))))))))))))))))
  (allB_succ 27 247 (allA_succ_of_accept 26 27 247 (accept_3_3 26 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 27 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 247 (accept_3_3 23 27 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  27 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 247 (accept_3_3 20 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 247 (Polychromatic418967fa.accept_15_4_12_7_1_3115 19 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 247 (accept_3_3 17 27 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 247 (accept_3_3 14 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 247 (Polychromatic418967fa.accept_17_13_10_9_1_946 13 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 27 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 247 (accept_3_3 11 27 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 247
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 247 (accept_3_3 8 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  247 (Polychromatic418967fa.accept_21_7_6_16_1_5834 7 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 247 (Polychromatic418967fa.accept_15_6_12_7_1_1360 6 27 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 247 (accept_3_3 5 27 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 247 (accept_3_3 2 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  247 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 27 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 247))))))))))))))))))))))))))) (allB_succ 26 247 (allA_of_3_1 26 26 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 25 247 (allA_succ_of_accept 24 25 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 25 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 247 (accept_3_3 23 25 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  25 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 247 (accept_3_3 20 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 247 (accept_3_3 17 25 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 247 (Polychromatic418967fa.accept_14_2_11_9_1_2925 16 25 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 247 (accept_3_3 14 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 25 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 247 (accept_3_3 11 25 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 247
  (Polychromatic418967fa.accept_20_9_5_7_1_6336 9 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 247 (accept_3_3 8 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  247 (Polychromatic418967fa.accept_21_7_4_16_1_5888 7 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 247 (accept_3_3 5 25 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 25 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 247 (accept_3_3 2 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  247 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 25 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 247))))))))))))))))))))))))) (allB_succ 24 247 (allA_succ_of_accept 23 24 247 (accept_3_3 23 24 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 22
  24 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 24 247 (accept_3_3 20 24 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  24 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 24 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 24 247 (Polychromatic418967fa.accept_21_18_3_16_1_5833 18 24 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 247 (accept_3_3 17 24 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 24 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 247
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 24 247 (accept_3_3 14 24 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  24 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 24 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 24 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 24 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 247 (accept_3_3 11 24 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 24 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 247
  (Polychromatic418967fa.accept_16_9_8_7_1_4529 9 24 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 24 247 (accept_3_3 8 24 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24
  247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 24 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 24 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 247 (accept_3_3 5 24 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 24 247 (Polychromatic418967fa.accept_16_4_8_7_1_3396 4 24 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  24 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 247 (accept_3_3 2 24 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 24
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 247)))))))))))))))))))))))) (allB_succ
  23 247 (allA_of_3_1 23 23 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 247 (allA_succ_of_accept 21 22
  247 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 247 (accept_3_3 20 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 247 (Polychromatic418967fa.accept_20_18_2_7_1_6285 18 22 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 247 (accept_3_3 17 22 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 22 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 247 (accept_3_3 14 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 247 (Polychromatic418967fa.accept_17_12_5_9_1_6372 12 22 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 247 (accept_3_3 11 22 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 22 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 247 (accept_3_3 8 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  247 (Polychromatic418967fa.accept_17_7_5_9_1_7763 7 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 22 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 22 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 247 (accept_3_3 5 22 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 22 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 247 (accept_3_3 2 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22
  247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 247)))))))))))))))))))))) (allB_succ 21 247 (allA_succ_of_accept 20 21 247 (accept_3_3 20 21 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 21 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 247 (accept_3_3 17 21 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  21 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 21 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 247 (accept_3_3 14 21 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 247 (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 21 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 247
  (Polychromatic418967fa.accept_14_12_7_9_1_726 12 21 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 247 (accept_3_3 11 21 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 247 (Polychromatic418967fa.accept_18_9_3_13_1_5905 9 21 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 247 (accept_3_3 8 21 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 21 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 247 (accept_3_3 5 21 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 247 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 21 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 247 (accept_3_3 2 21 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 21 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 247))))))))))))))))))))) (allB_succ 20 247 (allA_of_3_1 20 20
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 247 (allA_succ_of_accept 18 19 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 19 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 247 (accept_3_3 17 19 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 19 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 19 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 247 (accept_3_3 14 19 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 247 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 19 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 247
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 19 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 247 (accept_3_3 11 19 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 19 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 247 (Polychromatic418967fa.accept_16_9_3_7_1_6883 9 19 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 247 (accept_3_3 8 19 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 19 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 247 (accept_3_3 5 19 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  247 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 19 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 19 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 247 (accept_3_3 2 19 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 247 (Polychromatic418967fa.accept_21_1_19_16_1_2901 1 19 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 247))))))))))))))))))) (allB_succ 18 247 (allA_succ_of_accept 17
  18 247 (accept_3_3 17 18 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 247
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 16 18 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 247 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 18 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 247 (accept_3_3 14 18 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 12
  18 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 247 (accept_3_3 11 18
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 247
  (Polychromatic418967fa.accept_15_10_3_7_1_715 10 18 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 18 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 247 (accept_3_3 8 18 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 18 247 (Polychromatic418967fa.accept_26_7_18_13_1_14814 7 18 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 18 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 247 (accept_3_3 5 18 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18
  247 (Polychromatic418967fa.accept_15_4_3_7_1_713 4 18 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 18 247 (Polychromatic418967fa.accept_17_3_1_9_1_9012 3 18 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 247 (accept_3_3 2 18 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 18 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 247)))))))))))))))))) (allB_succ 17 247 (allA_of_3_1 17 17 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 247 (allA_succ_of_accept 15 16 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 247 (accept_3_3 14 16 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 247 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 16 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 16 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 247 (accept_3_3 11 16 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 16 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 247 (accept_3_3 8 16 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  247 (Polychromatic418967fa.accept_14_7_2_9_1_2093 7 16 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 16 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 16 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 247 (accept_3_3 5 16 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 247 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 16 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 247 (accept_3_3 2 16 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16
  247 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 16 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 247)))))))))))))))) (allB_succ 15 247 (allA_succ_of_accept 14 15 247 (accept_3_3 14 15 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 15 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 15 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 15 247 (accept_3_3 11 15 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  15 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 15 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 15 247 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 15 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 247 (accept_3_3 8 15 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 15 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 247
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 247 (accept_3_3 5 15 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 247 (accept_3_3 2 15 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 15 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 247))))))))))))))) (allB_succ 14 247 (allA_of_3_1 14 14 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 247 (allA_succ_of_accept 12 13 247
  (Polychromatic418967fa.accept_25_12_13_22_1_14813 12 13 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 247 (accept_3_3 11 13 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 247 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 13 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 247 (accept_3_3 8 13 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 247 (Polychromatic418967fa.accept_21_7_13_16_1_9068
  7 13 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 247 (accept_3_3 5 13 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  247 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 13 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 13 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 247 (accept_3_3 2 13 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 13 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 247))))))))))))) (allB_succ 12 247 (allA_succ_of_accept 11 12
  247 (accept_3_3 11 12 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 10 12 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 247 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 12 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 247 (accept_3_3 8 12 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 6
  12 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 247 (accept_3_3 5 12 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 4
  12 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 247 (accept_3_3 2 12 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  247 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 12 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 247)))))))))))) (allB_succ 11 247 (allA_of_3_1 11 11 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 247 (allA_succ_of_accept 9 10 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 247 (accept_3_3 8 10 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 247
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 10 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 247 (accept_3_3 5 10 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  247 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 10 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 10 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 247 (accept_3_3 2 10 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 247)))))))))) (allB_succ 9 247 (allA_succ_of_accept 8
  9 247 (accept_3_3 8 9 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 247
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 9 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 247 (accept_3_3 5 9 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 247 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 9
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 247 (accept_3_3 2 9 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 247 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1
  9 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 247))))))))) (allB_succ 8 247
  (allA_of_3_1 8 8 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 247 (allA_succ_of_accept 6 7 247
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 247 (accept_3_3 5 7 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 247
  (Polychromatic418967fa.accept_18_4_7_13_1_3303 4 7 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 7 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 247 (accept_3_3 2 7 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 247))))))) (allB_succ 6 247 (allA_succ_of_accept 5 6 247
  (accept_3_3 5 6 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 6 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 247 (accept_3_3 2 6 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 247)))))) (allB_succ 5 247 (allA_of_3_1 5 5 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 247 (allA_succ_of_accept 3 4 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 247 (accept_3_3 2 4 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 247
  (Polychromatic418967fa.accept_10_1_4_7_1_374 1 4 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 247)))) (allB_succ 3 247 (allA_succ_of_accept 2 3 247 (accept_3_3 2 3 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 3 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 247))) (allB_succ 2 247 (allA_of_3_1 2 2 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  247)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


