-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch259_Segment000
-- name    : Polychromatic418967fa_Branch259_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:54.397327+00:00
-- url     : https://prove2.me/theorems/ca313f11-09e8-4b16-92d5-95dc67ad28a3
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

def Polychromatic418967fa.branch_259_segment_000 : allB 123 259 :=
  allB_succ 122 259 (allA_of_3_1 122 122 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 121 259
  (allA_succ_of_accept 120 121 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 120 121 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 259 (accept_3_3 119 121 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 259
  (Polychromatic418967fa.accept_14_5_9_7_1_590 117 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 121 259 (accept_3_3 116 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 121 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 115 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 259 (accept_3_3 113 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 112 121
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 121 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 111 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 121 259 (accept_3_3 110 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 121 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 109 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 121 259 (Polychromatic418967fa.accept_10_8_1_9_1_413 108 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 121 259 (accept_3_3 107 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 121
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 105 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 121 259 (accept_3_3 104 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 121 259 (Polychromatic418967fa.accept_14_5_9_7_1_590 103 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 259 (accept_3_3 101 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 100 121 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 259
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 99 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 259 (accept_3_3 98 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 259 (Polychromatic418967fa.accept_17_12_2_4_1_11050 97 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 259 (accept_3_3 95 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 93 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 259 (accept_3_3 92 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 259 (accept_3_3 89 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 259 (Polychromatic418967fa.accept_10_8_1_9_1_413 88 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 87 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 259 (accept_3_3 86 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 85 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 259 (accept_3_3 83 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 259
  (Polychromatic418967fa.accept_13_3_4_12_1_36 81 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 259 (accept_3_3 80 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 259 (Polychromatic418967fa.accept_19_3_7_12_1_9105 79 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 259 (accept_3_3 77 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 259 (Polychromatic418967fa.accept_13_11_4_12_1_3585 76 121 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 259 (accept_3_3 74 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 259 (accept_3_3 71 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 121 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 69 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 259 (accept_3_3 68 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 259 (Polychromatic418967fa.accept_13_2_4_12_1_745 67 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 259 (accept_3_3 65 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 259
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 121 259 (accept_3_3 62 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 121 259 (Polychromatic418967fa.accept_14_5_9_7_1_590 61 121 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 121 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 259 (accept_3_3 59 121 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 259 (accept_3_3 56 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 259 (accept_3_3 53 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 52 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 51 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 259 (accept_3_3 50 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 259 (Polychromatic418967fa.accept_17_15_2_4_1_2423 49 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 259 (accept_3_3 47 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 259
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 259 (accept_3_3 44 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 259 (Polychromatic418967fa.accept_17_9_2_4_1_3472 43 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 259 (accept_3_3 41 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 259 (Polychromatic418967fa.accept_14_12_9_7_1_2762 40 121 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 259 (accept_3_3 38 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 259 (Polychromatic418967fa.accept_25_11_21_9_1_12308 36 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 259 (accept_3_3 35 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 259 (accept_3_3 32 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 259 (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 259 (accept_3_3 29 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 259
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 27 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 259 (accept_3_3 26 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 259 (accept_3_3 23 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 259 (accept_3_3 20 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 259 (accept_3_3 17 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 259 (Polychromatic418967fa.accept_13_3_4_12_1_36 16 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 259 (accept_3_3 14 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 259 (Polychromatic418967fa.accept_21_13_16_7_1_3712 13 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 259 (accept_3_3 11 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 259
  (Polychromatic418967fa.accept_17_9_2_4_1_3472 9 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 259 (accept_3_3 8 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 259 (accept_3_3 5 121 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 259 (Polychromatic418967fa.accept_18_4_13_7_1_5395 4 121 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 259 (accept_3_3 2 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 121 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 259 (allA_succ_of_accept 119 120 259 (accept_3_3 119 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 118 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 120 259 (Polychromatic418967fa.accept_16_5_8_3_1_4240 117 120
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 259 (accept_3_3 116 120
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 120 259
  (Polychromatic418967fa.accept_11_5_10_6_1_793 115 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 120 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 114 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 120 259 (accept_3_3 113 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 120 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 112 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 259
  (Polychromatic418967fa.accept_14_13_8_7_1_1224 111 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 120 259 (accept_3_3 110 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 109 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 120 259 (Polychromatic418967fa.accept_13_4_3_12_1_2066 108
  120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 259 (accept_3_3 107
  120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 259
  (Polychromatic418967fa.accept_13_2_3_12_1_735 106 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 120 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 105 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 120 259 (accept_3_3 104 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 120 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 103 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 120 259
  (Polychromatic418967fa.accept_21_18_15_7_1_9864 102 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 120 259 (accept_3_3 101 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 100 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 259 (Polychromatic418967fa.accept_14_1_8_7_1_1253 99 120
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 120 259 (accept_3_3 98 120
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 120 259
  (Polychromatic418967fa.accept_14_13_8_7_1_1224 97 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 120 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 96 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 120 259 (accept_3_3 95 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 120 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 94 120 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 259 (Polychromatic418967fa.accept_11_5_10_6_1_793
  93 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 259 (accept_3_3 92
  120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 120 259
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 120 259 (Polychromatic418967fa.accept_14_6_8_7_1_589 90 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 120 259 (accept_3_3 89 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 120 259 (Polychromatic418967fa.accept_28_4_8_7_1_15788 88 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 87 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 120 259 (accept_3_3 86 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 120 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 85 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 120 259 (Polychromatic418967fa.accept_16_4_8_3_1_4206 84 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 120 259 (accept_3_3 83 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 120 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 259
  (Polychromatic418967fa.accept_21_18_15_7_1_9864 81 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 120 259 (accept_3_3 80 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 120 259 (Polychromatic418967fa.accept_25_4_20_9_1_15787 79 120 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 120 259 (Polychromatic418967fa.accept_9_6_3_7_1_580
  78 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 259 (accept_3_3 77
  120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 76 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 120 259 (Polychromatic418967fa.accept_16_11_8_3_1_3183 75 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 120 259 (accept_3_3 74 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 120 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 120 259
  (Polychromatic418967fa.accept_19_15_6_12_1_7746 72 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 120 259 (accept_3_3 71 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 120 259 (Polychromatic418967fa.accept_19_13_6_12_1_6109 70 120 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 120 259 (Polychromatic418967fa.accept_9_6_3_7_1_580
  69 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 259 (accept_3_3 68
  120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 120 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 120 259 (Polychromatic418967fa.accept_21_3_15_7_1_5155 66 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 120 259 (accept_3_3 65 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 120 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 259
  (Polychromatic418967fa.accept_31_1_27_11_1_15786 63 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 120 259 (accept_3_3 62 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 259 (Polychromatic418967fa.accept_13_9_3_12_1_2025 61 120 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 120 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 120 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 120 259 (accept_3_3 59 120 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 259 (Polychromatic418967fa.accept_9_4_3_7_1_296
  58 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 259
  (Polychromatic418967fa.accept_14_1_8_7_1_1253 57 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 120 259 (accept_3_3 56 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 120 259 (Polychromatic418967fa.accept_13_2_3_12_1_735 54 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 120 259 (accept_3_3 53 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 259 (Polychromatic418967fa.accept_16_4_8_3_1_4206 52 120
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 120 259 (accept_3_3 50 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 120 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 120 259 (Polychromatic418967fa.accept_13_9_3_12_1_2025 48 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 259 (accept_3_3 47 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 120 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 259
  (Polychromatic418967fa.accept_16_13_8_3_1_5374 45 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 120 259 (accept_3_3 44 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 120 259 (Polychromatic418967fa.accept_13_4_3_12_1_2066 43 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 120 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 120 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 120 259 (accept_3_3 41 120 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 259
  (Polychromatic418967fa.accept_17_5_1_4_1_3460 39 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 120 259 (accept_3_3 38 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 120 259 (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 120 259 (accept_3_3 35 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 259 (Polychromatic418967fa.accept_14_6_8_7_1_589 34 120
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 120 259 (accept_3_3 32 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 120 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 120 259 (Polychromatic418967fa.accept_13_4_3_12_1_2066 30 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 120 259 (accept_3_3 29 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 120 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 259
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 120 259 (accept_3_3 26 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 120 259 (Polychromatic418967fa.accept_17_8_1_4_1_9831 25 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 120 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 120 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 259 (accept_3_3 23 120 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 259
  (Polychromatic418967fa.accept_16_5_8_3_1_4240 21 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 120 259 (accept_3_3 20 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 120 259 (Polychromatic418967fa.accept_19_18_6_12_1_6250 18 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 259 (accept_3_3 17 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 259 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 120
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 120 259 (accept_3_3 14 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 120 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 120 259 (Polychromatic418967fa.accept_16_12_8_3_1_4241 12 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 259 (accept_3_3 11 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 120 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 259
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 120 259 (accept_3_3 8 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  120 259 (Polychromatic418967fa.accept_22_7_10_17_1_7956 7 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 120 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 120 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 259 (accept_3_3 5 120 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 120 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 259
  (Polychromatic418967fa.accept_18_3_12_7_1_6728 3 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 120 259 (accept_3_3 2 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  120 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 120
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 259 (allA_of_3_1 119 119 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 118 259
  (allA_succ_of_accept 117 118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 118 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 118 259 (accept_3_3 116 118 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 118 259 (Polychromatic418967fa.accept_13_11_1_12_1_742 115 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 118 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 114 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 118 259 (accept_3_3 113 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 118 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 112 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 118 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 118 259 (accept_3_3 110 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 109 118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 118 259
  (Polychromatic418967fa.accept_25_8_18_9_1_15785 108 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 118 259 (accept_3_3 107 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 118 259 (Polychromatic418967fa.accept_13_2_1_12_1_1326 106 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9
  105 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 118 259 (accept_3_3
  104 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 118 259
  (Polychromatic418967fa.accept_9_4_1_7_1_293 103 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 118 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 102 118 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 118 259 (accept_3_3 101 118 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 118 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 100 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 118 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 118 259 (accept_3_3 98 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 118 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 118 259 (accept_3_3 95 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 118 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 118 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 118 259 (accept_3_3 92 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 118 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 91 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 118 259 (Polychromatic418967fa.accept_17_5_16_4_1_4734 90 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 118 259 (accept_3_3 89 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 118 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 118
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 118 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 118 259 (accept_3_3 86 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 118 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 118 259 (accept_3_3 83 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 118 259 (Polychromatic418967fa.accept_16_2_6_3_1_5396 82 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 118 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 118 259 (accept_3_3 80 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 118 259 (Polychromatic418967fa.accept_21_16_13_7_1_8385 79 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 118 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 118 259 (accept_3_3 77 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 118 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 118 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 118 259 (accept_3_3 74 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 118 259 (Polychromatic418967fa.accept_21_9_13_7_1_5154 72 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 118 259 (accept_3_3 71 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 118 259 (Polychromatic418967fa.accept_13_5_1_12_1_740 70 118
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 118 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 118 259 (accept_3_3 68 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 118 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 118 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 118 259 (accept_3_3 65 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 118 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 64 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 118 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 118 259 (accept_3_3 62 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 118 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 118 259 (accept_3_3 59 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 118 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 118 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 118 259 (accept_3_3 56 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 118 259 (Polychromatic418967fa.accept_14_13_6_7_1_2013 55 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 118 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 118 259 (accept_3_3 53 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 118 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 118
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 118 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 118 259 (accept_3_3 50 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 118 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 118 259 (accept_3_3 47 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 118 259 (Polychromatic418967fa.accept_19_8_4_12_1_4768 46 118 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 118 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 118 259 (accept_3_3 44 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 118 259 (Polychromatic418967fa.accept_14_1_6_7_1_1936 43 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 118 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 118 259 (accept_3_3 41 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 118 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 118 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 118 259 (accept_3_3 38 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 118 259 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 118 259 (accept_3_3 35 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 118 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 118
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 118 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 118 259 (accept_3_3 32 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 118 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 118 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 118 259 (accept_3_3 29 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 118 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 118 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 118 259 (accept_3_3 26 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 118 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 118 259 (accept_3_3 23 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 118 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 118 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 118 259 (accept_3_3 20 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 118 259 (Polychromatic418967fa.accept_21_19_13_7_1_3706 19 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 118 259 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 259 (accept_3_3 17 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 118
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 118 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 118 259 (accept_3_3 14 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 118 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 259 (accept_3_3 11 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 118 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 118 259 (accept_3_3 8 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  118 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 118 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 259 (accept_3_3 5 118 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 118 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 118 259 (accept_3_3 2 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  118 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 118
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 259 (allA_succ_of_accept 116 117 259 (accept_3_3 116 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 259 (Polychromatic418967fa.accept_20_15_17_19_1_10076 115 117 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 259 (Polychromatic418967fa.accept_4_2_1_3_1_27
  114 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 259 (accept_3_3
  113 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 259
  (Polychromatic418967fa.accept_6_4_3_1_1_57 112 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 117 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 111 117 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 259 (accept_3_3 110 117 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 117 259 (Polychromatic418967fa.accept_21_4_12_7_1_5174 109 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 259
  (Polychromatic418967fa.accept_10_8_7_9_1_425 108 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 117 259 (accept_3_3 107 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 117 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 117 259 (Polychromatic418967fa.accept_19_10_3_12_1_10566 105 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 259 (accept_3_3 104 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 259 (Polychromatic418967fa.accept_21_19_12_7_1_15784 103
  117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 117 259 (accept_3_3 101 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 117 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 117 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 99 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 259 (accept_3_3 98 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 259 (Polychromatic418967fa.accept_15_7_12_4_1_1236 97 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 259
  (Polychromatic418967fa.accept_14_12_5_7_1_2010 96 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 117 259 (accept_3_3 95 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 117 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 117 259 (Polychromatic418967fa.accept_14_9_5_7_1_1251 93 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 259 (accept_3_3 92 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 259 (Polychromatic418967fa.accept_15_1_12_4_1_2022 91 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 117 259 (accept_3_3 89 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 117 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 117 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 87 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 259 (accept_3_3 86 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 259 (Polychromatic418967fa.accept_19_9_3_12_1_6191 85 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 259
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 84 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 117 259 (accept_3_3 83 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 117 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 117 259 (Polychromatic418967fa.accept_21_18_12_7_1_6712 81 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 259 (accept_3_3 80 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 259 (Polychromatic418967fa.accept_14_9_5_7_1_1251 79 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 117 259 (accept_3_3 77 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 117 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 117 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 75 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 259 (accept_3_3 74 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 259 (Polychromatic418967fa.accept_23_4_2_6_1_9259 73 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 259
  (Polychromatic418967fa.accept_10_2_7_9_1_783 72 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 117 259 (accept_3_3 71 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 117 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 117 259 (Polychromatic418967fa.accept_15_9_12_4_1_2023 69 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 259 (accept_3_3 68 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 67 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 117 259 (accept_3_3 65 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 117 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 117 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 259 (accept_3_3 62 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 259 (Polychromatic418967fa.accept_15_1_12_4_1_2022 61 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 259
  (Polychromatic418967fa.accept_18_6_9_7_1_2905 60 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 117 259 (accept_3_3 59 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 117 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 117 259 (Polychromatic418967fa.accept_18_3_9_7_1_1839 57 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 259 (accept_3_3 56 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 259 (Polychromatic418967fa.accept_19_17_3_12_1_13140 55
  117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 117 259 (accept_3_3 53 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 117 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 117 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 51 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 259 (accept_3_3 50 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 259 (Polychromatic418967fa.accept_19_11_3_12_1_6138 49 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 259
  (Polychromatic418967fa.accept_10_8_7_9_1_425 48 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 117 259 (accept_3_3 47 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 117 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 117 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 259 (accept_3_3 44 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 259 (Polychromatic418967fa.accept_21_1_12_7_1_3783 43 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 259 (accept_3_3 41 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 117 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 259 (accept_3_3 38 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 259 (Polychromatic418967fa.accept_14_9_5_7_1_1251 37 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 259
  (Polychromatic418967fa.accept_17_2_15_4_1_4723 36 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 117 259 (accept_3_3 35 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 117 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 259 (Polychromatic418967fa.accept_17_16_15_4_1_8559 33 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 259 (accept_3_3 32 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 259 (Polychromatic418967fa.accept_15_1_12_4_1_2022 31 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 117 259 (accept_3_3 29 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 117 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 259 (accept_3_3 26 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 259 (Polychromatic418967fa.accept_21_4_12_7_1_5174 25 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 259
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 24 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 259 (accept_3_3 23 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 259 (Polychromatic418967fa.accept_18_3_9_7_1_1839 21 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 259 (accept_3_3 20 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 259 (Polychromatic418967fa.accept_17_2_15_4_1_4723 19 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 259 (accept_3_3 17 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 15 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 259 (accept_3_3 14 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 259 (Polychromatic418967fa.accept_19_13_3_12_1_6186 13 117
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 259
  (Polychromatic418967fa.accept_10_2_7_9_1_783 12 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 259 (accept_3_3 11 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 259 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 117 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 259 (accept_3_3 8 117 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 259 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 259 (accept_3_3 5 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 117 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 259 (accept_3_3 2 117 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 117 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 259 (allA_of_3_1 116 116 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 259
  (allA_succ_of_accept 114 115 259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 114 115 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 259 (accept_3_3 113 115 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 112 115 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 112 115 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 259
  (Polychromatic418967fa.accept_10_1_5_9_1_157 111 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 115 259 (accept_3_3 110 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 115 259 (Polychromatic418967fa.accept_11_10_5_6_1_1842 109 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 115 259 (Polychromatic418967fa.accept_13_4_11_12_1_1318 108 115 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 115 259 (accept_3_3 107 115 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 115 259
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 106 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 115 259 (Polychromatic418967fa.accept_13_1_11_12_1_1322 105 115 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 115 259 (accept_3_3 104 115 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 115 259 (Polychromatic418967fa.accept_15_13_10_4_1_1232 103 115 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 259
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 102 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 115 259 (accept_3_3 101 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 115 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 100 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 115 259 (Polychromatic418967fa.accept_15_9_10_4_1_2055 99 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 115 259 (accept_3_3 98 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 115 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 97 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 115 259
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 96 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 115 259 (accept_3_3 95 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 115 259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 94 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 115 259 (Polychromatic418967fa.accept_17_8_13_4_1_6012 93 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 115 259 (accept_3_3 92 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 115 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 91 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 115 259
  (Polychromatic418967fa.accept_20_10_15_19_1_12983 90 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 115 259 (accept_3_3 89 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 115 259 (Polychromatic418967fa.accept_13_10_11_12_1_1320 88 115 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 259
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 87 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 259 (accept_3_3 86 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 115 259 (Polychromatic418967fa.accept_13_7_11_12_1_2051 85 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 115 259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 84 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 259 (accept_3_3 83 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 259 (Polychromatic418967fa.accept_13_4_11_12_1_1318 82 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 259
  (Polychromatic418967fa.accept_10_1_5_9_1_157 81 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 115 259 (accept_3_3 80 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 115 259 (Polychromatic418967fa.accept_13_1_11_12_1_1322 79 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 115 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 78 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 259 (accept_3_3 77 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 115 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 76 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 259
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 75 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 115 259 (accept_3_3 74 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 115 259 (Polychromatic418967fa.accept_15_13_10_4_1_1232 73 115 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 259
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 115 259 (accept_3_3 71 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 115 259 (Polychromatic418967fa.accept_19_13_1_12_1_11768 70 115 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 115 259
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 69 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 115 259 (accept_3_3 68 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 115 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 67 115 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 66 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 259 (accept_3_3 65 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 115 259
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 64 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 115 259 (Polychromatic418967fa.accept_22_19_5_17_1_9630 63 115 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 259 (accept_3_3 62 115 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 259
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 60 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 115 259 (accept_3_3 59 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 115 259 (Polychromatic418967fa.accept_15_13_10_4_1_1232 58 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 115 259 (Polychromatic418967fa.accept_20_17_15_19_1_12975 57 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 259 (accept_3_3 56 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 115 259 (Polychromatic418967fa.accept_21_13_10_7_1_3701 55 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 259
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 259 (accept_3_3 53 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 259 (Polychromatic418967fa.accept_14_10_3_7_1_1975 52 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 259 (accept_3_3 50 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 259 (Polychromatic418967fa.accept_13_10_11_12_1_1320 49
  115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 259
  (Polychromatic418967fa.accept_17_14_13_4_1_13402 48 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 115 259 (accept_3_3 47 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 115 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 46 115 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 259 (accept_3_3 44 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 259
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 115 259 (Polychromatic418967fa.accept_17_8_13_4_1_6012 42 115 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 259 (accept_3_3 41 115 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 115 259 (Polychromatic418967fa.accept_13_1_11_12_1_1322 40 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 259
  (Polychromatic418967fa.accept_14_11_3_7_1_604 39 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 259 (accept_3_3 38 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 37 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 259 (accept_3_3 35 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 34 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 259
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 115 259 (accept_3_3 32 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 115 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 115 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 259 (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 259 (accept_3_3 29 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 259
  (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 259 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 259 (accept_3_3 26 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 259 (Polychromatic418967fa.accept_14_11_3_7_1_604 25 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 259
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 259 (accept_3_3 23 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 259 (accept_3_3 20 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 259 (Polychromatic418967fa.accept_21_19_10_7_1_8384 19 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 259
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 18 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 259 (accept_3_3 17 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 259 (Polychromatic418967fa.accept_21_15_10_7_1_9837 15 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 259 (accept_3_3 14 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 259 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 259
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 259 (accept_3_3 11 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 259 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 259 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 259 (accept_3_3 8 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 259 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 115
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 259
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 259 (accept_3_3 5 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 115 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 259 (Polychromatic418967fa.accept_17_3_13_4_1_8530 3 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 259 (accept_3_3 2 115 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 115 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 259 (allA_succ_of_accept 113 114 259 (accept_3_3 113 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 114 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 112 114 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 114 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 111 114
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 259 (accept_3_3 110 114
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 114 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 114 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 108 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 259 (accept_3_3 107 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 259 (Polychromatic418967fa.accept_13_2_10_12_1_757 106 114 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 114 259 (accept_3_3 104 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 114 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 103 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 114 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 102 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 259 (accept_3_3 101 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 100 114
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 259
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 99 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 114 259 (accept_3_3 98 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 114 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 114 259 (Polychromatic418967fa.accept_14_12_2_7_1_1243 96 114
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 259 (accept_3_3 95 114
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 259
  (Polychromatic418967fa.accept_9_4_6_7_1_286 94 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 114 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 259 (accept_3_3 92 114 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 114 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 114 259 (Polychromatic418967fa.accept_11_2_4_6_1_2412
  90 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 114 259 (accept_3_3 89
  114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 259
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 88 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 114 259 (Polychromatic418967fa.accept_13_9_10_12_1_2048 87 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 259 (accept_3_3 86 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 114 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 114 259 (accept_3_3 83 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 114 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 259 (accept_3_3 80 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 259 (Polychromatic418967fa.accept_11_2_4_6_1_2412 79 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 114 259
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 78 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 114 259 (accept_3_3 77 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 114 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 114 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 259 (accept_3_3 74 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 114 259
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 114 259 (accept_3_3 71 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 114 259 (Polychromatic418967fa.accept_15_10_9_4_1_2924 70 114 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 114 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 259 (accept_3_3 68 114 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 259 (Polychromatic418967fa.accept_9_4_6_7_1_286
  67 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 114 259 (accept_3_3 65 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 114 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 114 259 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 259 (accept_3_3 62 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 259
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 60 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 114 259 (accept_3_3 59 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 114 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 114 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 114 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 259 (accept_3_3 56 114 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 259 (Polychromatic418967fa.accept_9_1_6_7_1_285
  55 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 259
  (Polychromatic418967fa.accept_13_2_10_12_1_757 54 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 114 259 (accept_3_3 53 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 114 259 (Polychromatic418967fa.accept_21_10_9_7_1_9857 52 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 114 259 (Polychromatic418967fa.accept_14_9_2_7_1_1242 51 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 259 (accept_3_3 50 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 114 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 114 259 (accept_3_3 47 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 114 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 259 (accept_3_3 44 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 259 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 259
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 42 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 114 259 (accept_3_3 41 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 114 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 114 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 259 (accept_3_3 38 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 259
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 114 259 (accept_3_3 35 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 114 259 (Polychromatic418967fa.accept_13_8_10_12_1_1337 34 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 259 (accept_3_3 32 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 259 (accept_3_3 29 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 114 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 259 (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 259 (accept_3_3 26 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 259
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 114 259 (accept_3_3 23 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 114 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 259 (accept_3_3 20 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 259
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 259 (accept_3_3 17 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 114 259 (Polychromatic418967fa.accept_21_16_9_7_1_6709 16 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 259 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 259 (accept_3_3 14 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 259 (accept_3_3 11 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 114 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 259 (accept_3_3 8 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 259 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 259
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 259 (accept_3_3 5 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  114 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 114 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 259 (accept_3_3 2 114 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 259 (allA_of_3_1 113 113 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 259
  (allA_succ_of_accept 111 112 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 112 259 (accept_3_3 110 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 112 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 109 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 112 259
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 108 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 112 259 (accept_3_3 107 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 112 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 106 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 112 259 7 15 16 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 112 259 (accept_3_3 104 112 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 112 259 (Polychromatic418967fa.accept_11_4_2_6_1_389 103 112
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 112 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 102 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 112 259 (accept_3_3 101 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 112 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 100 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 112 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 112 259 7 14 16 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 112 259
  (Polychromatic418967fa.accept_10_7_2_9_1_775 97 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 112 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 112 259 (accept_3_3 95 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 112 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 94 112 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 112 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 112 259 (accept_3_3 92 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91
  112 259 7 13 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 90 112 259 (Polychromatic418967fa.accept_19_14_17_12_1_6099 90 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 112 259 (accept_3_3 89 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 112 259 (Polychromatic418967fa.accept_13_10_8_12_1_2032 88 112 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 112 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 112 259 (accept_3_3 86 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 112 259 (Polychromatic418967fa.accept_13_7_8_12_1_2810 85 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 112 259 7 12 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 112 259 (accept_3_3 83 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 112 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 112 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 112 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 112 259 (accept_3_3 80 112 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 112 259
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 79 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 112 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 78 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 112 259 7 11 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 112 259
  (Polychromatic418967fa.accept_25_1_12_9_1_15783 76 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 112 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 112 259 (accept_3_3 74 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 112 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 112 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 112 259
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 112 259 (accept_3_3 71 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  112 259 7 10 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 112 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 112 259 (accept_3_3 68 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 112 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 67 112 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 112 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 112 259 (accept_3_3 65 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 112 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 112 259 7 9 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 112 259 (accept_3_3 62 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 112 259 (Polychromatic418967fa.accept_10_1_2_9_1_152 61 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 112 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 112 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 259 (accept_3_3 59 112 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 112 259 (Polychromatic418967fa.accept_12_10_4_7_1_948
  58 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 112 259 7 8 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 112 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 112 259 (Polychromatic418967fa.accept_31_23_19_11_1_15782 54
  112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 259 (accept_3_3 53
  112 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 259
  (Polychromatic418967fa.accept_18_16_4_7_1_2927 52 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 112 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 112 259 (accept_3_3 50 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 49 112 259 7 7 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 48 112 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 112 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 259 (accept_3_3 47 112 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 112 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 259 (accept_3_3 44 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 259 (Polychromatic418967fa.accept_13_4_8_12_1_3526 43 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 112 259 7 6 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 112 259 (accept_3_3 41 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 112 259 (Polychromatic418967fa.accept_13_1_8_12_1_2045 40 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 112 259 (accept_3_3 38 112 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 112 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 37
  112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 259
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 112 259 7 5 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 112 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 112 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 259 (accept_3_3 32 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 259 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 259 (accept_3_3 29 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 259 7 4 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 259 (accept_3_3 26 112 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 112 259
  (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 112 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 259 (accept_3_3 23 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 112 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 112 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 112 259 7 3 16 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 112 259 (accept_3_3 20 112 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 112 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19
  112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 259
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 112 259 (accept_3_3 17 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 112 259 (Polychromatic418967fa.accept_18_16_4_7_1_2927 16 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 112 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 112 259 7 2 16 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 112 259
  (Polychromatic418967fa.accept_18_13_4_7_1_4086 13 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 112 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 259 (accept_3_3 11 112 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 112 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 9
  112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 259 (accept_3_3 8 112
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 112 259 7 1 16 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 112 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 259 (accept_3_3 5 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 259 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 112 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 259 (accept_3_3 2 112 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 259 (allA_succ_of_accept 110 111 259 (accept_3_3 110 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 109 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 108 111
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 259 (accept_3_3 107 111
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 259
  (Polychromatic418967fa.accept_6_4_3_1_1_57 106 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 111 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 105 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 259 (accept_3_3 104 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 111 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 103 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 259
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 102 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 111 259 (accept_3_3 101 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 111 259 (Polychromatic418967fa.accept_13_8_7_12_1_3637 99 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 259 (accept_3_3 98 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 259 (Polychromatic418967fa.accept_13_6_7_12_1_3504 97 111
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 96 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 111 259 (accept_3_3 95 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 111 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 93 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 259 (accept_3_3 92 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 91 111 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 259
  (Polychromatic418967fa.accept_14_6_13_7_1_2015 90 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 111 259 (accept_3_3 89 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 111 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 259 (accept_3_3 86 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 85 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 259
  (Polychromatic418967fa.accept_8_4_7_3_1_144 84 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 259 (accept_3_3 83 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 111 259 (Polychromatic418967fa.accept_12_9_3_7_1_924 81 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 259 (accept_3_3 80 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 259 (Polychromatic418967fa.accept_21_16_6_7_1_6764 79 111
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 259 (accept_3_3 77 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 75 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 111 259 37 2 3 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 111 259
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 111 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 259 (accept_3_3 71 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 259 (Polychromatic418967fa.accept_9_6_3_7_1_580
  69 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 259 (accept_3_3 68
  111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 111 259 (Polychromatic418967fa.accept_16_2_15_3_1_1300 66 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 259 (accept_3_3 65 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 111 259
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 259 (accept_3_3 62 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 259 (Polychromatic418967fa.accept_16_13_15_3_1_4196 61 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 259 (Polychromatic418967fa.accept_8_4_7_3_1_144
  60 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 259 (accept_3_3 59
  111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 259
  (Polychromatic418967fa.accept_6_4_3_1_1_57 58 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 111 259 (Polychromatic418967fa.accept_12_9_3_7_1_924 57 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 259 (accept_3_3 56 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 111 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 259 (Polychromatic418967fa.accept_15_9_6_4_1_1220
  54 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 259 (accept_3_3 53
  111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 259
  (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 111 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 259 (accept_3_3 50 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 111 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 259 (Polychromatic418967fa.accept_10_8_1_9_1_413
  48 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 259 (accept_3_3 47
  111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 259
  (Polychromatic418967fa.accept_6_4_3_1_1_57 46 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 111 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 259 (accept_3_3 44 111 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 111 259 (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 259 (accept_3_3 41 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 259 (Polychromatic418967fa.accept_15_9_6_4_1_1220 39 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 259 (accept_3_3 38 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 37 111 259 37 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 36 111 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 111 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 259 (accept_3_3 35 111 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 34
  111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 111 259 (accept_3_3 32 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 111 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 111 259 (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 259 (accept_3_3 29 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 259
  (Polychromatic418967fa.accept_11_5_1_6_1_774 27 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 111 259 (accept_3_3 26 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 111 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 111 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 259 (accept_3_3 23 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 259 (accept_3_3 20 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 111 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 259 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 259 (accept_3_3 17 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 259 (accept_3_3 14 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 259 (accept_3_3 11 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 259 (accept_3_3 8 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 259 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 259 (accept_3_3 5 111 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 259
  (Polychromatic418967fa.accept_21_3_6_7_1_6750 3 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 259 (accept_3_3 2 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 111 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 259 (allA_of_3_1 110 110 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 259
  (allA_succ_of_accept 108 109 259 (Polychromatic418967fa.accept_13_4_5_12_1_751 108 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 259 (accept_3_3 107 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 105 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 259 (accept_3_3 104 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 103 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 259 (accept_3_3 101 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 259 (Polychromatic418967fa.accept_21_16_4_7_1_5191 100
  109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 259
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 99 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 259 (accept_3_3 98 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 259 (Polychromatic418967fa.accept_13_6_5_12_1_307 97 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 259 (accept_3_3 95 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 93 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 259 (accept_3_3 92 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 259 (Polychromatic418967fa.accept_33_25_10_28_1_15781 91 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 259 (accept_3_3 89 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 259 (Polychromatic418967fa.accept_14_4_11_7_1_1234 88 109
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 87 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 259 (accept_3_3 86 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 259 (accept_3_3 83 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 259
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 81 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 259 (accept_3_3 80 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 259 (Polychromatic418967fa.accept_13_1_5_12_1_306 79 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 259 (accept_3_3 77 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 75 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 259 (accept_3_3 74 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 259 (Polychromatic418967fa.accept_13_8_5_12_1_2755 73 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 259 (Polychromatic418967fa.accept_13_7_5_12_1_1305 72 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 259 (accept_3_3 71 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 109 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 69 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 259 (accept_3_3 68 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 259 (accept_3_3 65 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 259 (Polychromatic418967fa.accept_19_7_14_12_1_2261 64 109 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 259
  (Polychromatic418967fa.accept_16_15_13_3_1_4215 63 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 109 259 (accept_3_3 62 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 109 259 (Polychromatic418967fa.accept_21_19_4_7_1_3775 61 109 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 109 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 259 (accept_3_3 59 109 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 259 (accept_3_3 56 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 259 (Polychromatic418967fa.accept_19_17_14_12_1_2263 55 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 259 (accept_3_3 53 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 259 (Polychromatic418967fa.accept_14_10_11_7_1_1955 52 109
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 259 (accept_3_3 50 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 259 (accept_3_3 47 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 259
  (Polychromatic418967fa.accept_13_6_5_12_1_307 45 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 259 (accept_3_3 44 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 259 (Polychromatic418967fa.accept_13_4_5_12_1_751 43 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 259 (accept_3_3 41 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 259 (accept_3_3 38 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 259 (Polychromatic418967fa.accept_17_3_7_4_1_7230 37 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 259 (Polychromatic418967fa.accept_19_17_14_12_1_2263 36 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 259 (accept_3_3 35 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 259 (accept_3_3 32 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 259 (accept_3_3 29 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 259 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 109 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 259
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 259 (accept_3_3 26 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 259 (Polychromatic418967fa.accept_17_8_7_4_1_8617 25 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 259 (accept_3_3 23 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 259 (accept_3_3 20 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 259 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 259 (accept_3_3 17 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 259 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 259 (accept_3_3 14 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 259 (accept_3_3 11 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 259
  (Polychromatic418967fa.accept_19_9_14_12_1_7764 9 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 259 (accept_3_3 8 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 259 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 259 (accept_3_3 5 109 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 259 (accept_3_3 2 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 259 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 109 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 259 (allA_succ_of_accept 107 108 259 (accept_3_3 107 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 108 259 (Polychromatic418967fa.accept_13_2_4_12_1_745 106 108 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 259
  (Polychromatic418967fa.accept_16_9_12_3_1_3138 105 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 108 259 (accept_3_3 104 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 108 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 103 108 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 108 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 102 108
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 259 (accept_3_3 101 108
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 259
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 100 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 108 259 (Polychromatic418967fa.accept_13_8_4_12_1_2753 99 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 108 259 (accept_3_3 98 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 108 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 97 108
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 108 259
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 96 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 108 259 (accept_3_3 95 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 108 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 94 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 108 259 (Polychromatic418967fa.accept_13_2_4_12_1_745 93 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 108 259 (accept_3_3 92 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 108 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 91 108
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 108 259
  (Polychromatic418967fa.accept_16_10_12_3_1_4252 90 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 108 259 (accept_3_3 89 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 108 259 (Polychromatic418967fa.accept_14_4_10_7_1_1946 88 108 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 87 108 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 108 259 (accept_3_3 86 108 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 108 259
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 85 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 108 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 84 108 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 259 (accept_3_3 83 108 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 108 259 (Polychromatic418967fa.accept_15_7_3_4_1_574 82 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 259
  (Polychromatic418967fa.accept_10_1_8_9_1_787 81 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 108 259 (accept_3_3 80 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 108 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 108 259 (Polychromatic418967fa.accept_17_10_6_4_1_2506 78 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 259 (accept_3_3 77 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 259 (Polychromatic418967fa.accept_13_11_4_12_1_3585 76 108
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 259
  (Polychromatic418967fa.accept_19_18_13_12_1_4775 75 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 108 259 (accept_3_3 74 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 108 259 (Polychromatic418967fa.accept_13_8_4_12_1_2753 73 108 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 108 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 72 108
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 259 (accept_3_3 71 108
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 259
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 70 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 108 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 69 108 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 259 (accept_3_3 68 108 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 108 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 67 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 108 259
  (Polychromatic418967fa.accept_24_18_12_19_1_15780 66 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 108 259 (accept_3_3 65 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 108 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 64 108 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 108 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 259 (accept_3_3 62 108 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 259 (Polychromatic418967fa.accept_10_1_8_9_1_787
  61 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 108 259
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 60 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 108 259 (accept_3_3 59 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 108 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 58 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 108 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 57 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 259 (accept_3_3 56 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 108 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 259
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 108 259 (accept_3_3 53 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 108 259 (Polychromatic418967fa.accept_15_7_3_4_1_574 52 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 108 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 259 (accept_3_3 50 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 259 (Polychromatic418967fa.accept_19_11_13_12_1_6259 49
  108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 259
  (Polychromatic418967fa.accept_21_6_3_7_1_12873 48 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 108 259 (accept_3_3 47 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 108 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 46 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 108 259 (Polychromatic418967fa.accept_14_3_10_7_1_3773 45 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 259 (accept_3_3 44 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 259 (Polychromatic418967fa.accept_19_5_13_12_1_13154 43
  108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 259
  (Polychromatic418967fa.accept_13_3_4_12_1_36 42 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 108 259 (accept_3_3 41 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 108 259 (Polychromatic418967fa.accept_16_8_12_3_1_4194 40 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 108 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 108 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 259 (accept_3_3 38 108 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 37 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 259
  (Polychromatic418967fa.accept_11_3_9_6_1_105 36 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 108 259 (accept_3_3 35 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 108 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 108 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 259 (accept_3_3 32 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 108 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 259
  (Polychromatic418967fa.accept_19_11_13_12_1_6259 30 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 108 259 (accept_3_3 29 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 108 259 (Polychromatic418967fa.accept_13_2_4_12_1_745 28 108 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 108
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 259 (accept_3_3 26 108
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 259
  (Polychromatic418967fa.accept_11_3_9_6_1_105 25 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 108 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 108 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 259 (accept_3_3 23 108 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 108 259 (Polychromatic418967fa.accept_15_7_3_4_1_574 22 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 259
  (Polychromatic418967fa.accept_10_1_8_9_1_787 21 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 259 (accept_3_3 20 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 108 259 (Polychromatic418967fa.accept_17_2_6_4_1_2431 19 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 108 259 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 259 (accept_3_3 17 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 259 (Polychromatic418967fa.accept_13_3_4_12_1_36 16 108
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 259
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 108 259 (accept_3_3 14 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 108 259 (Polychromatic418967fa.accept_23_13_16_6_1_7665 13 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 108 259 (Polychromatic418967fa.accept_21_12_3_7_1_14223 12 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 259 (accept_3_3 11 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 259 (Polychromatic418967fa.accept_16_10_12_3_1_4252 10 108
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 259
  (Polychromatic418967fa.accept_16_9_12_3_1_3138 9 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 108 259 (accept_3_3 8 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  108 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 108 259 (Polychromatic418967fa.accept_19_6_13_12_1_6220 6 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 259 (accept_3_3 5 108 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 108 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 259
  (Polychromatic418967fa.accept_11_3_9_6_1_105 3 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 108 259 (accept_3_3 2 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  108 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 108 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 108
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 259 (allA_of_3_1 107 107 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 259
  (allA_succ_of_accept 105 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 106 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 259 (accept_3_3 104 106 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 106 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 103 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 259
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 102 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 106 259 (accept_3_3 101 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 106 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 100 106 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 106 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 106 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 259 (accept_3_3 98 106 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 97
  106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 259
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 96 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 259 (accept_3_3 95 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 259 (Polychromatic418967fa.accept_13_3_2_12_1_2797 94 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 259 (accept_3_3 92 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 259 (Polychromatic418967fa.accept_18_1_16_7_1_2897 91 106 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 259
  (Polychromatic418967fa.accept_14_6_8_7_1_589 90 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 106 259 (accept_3_3 89 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 106 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 106 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 259 (accept_3_3 86 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 259
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 84 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 259 (accept_3_3 83 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 259 (Polychromatic418967fa.accept_13_4_2_12_1_2800 82 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 259 (accept_3_3 80 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 259 (Polychromatic418967fa.accept_13_1_2_12_1_1299 79 106 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 259
  (Polychromatic418967fa.accept_11_1_7_6_1_378 78 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 259 (accept_3_3 77 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 259 (accept_3_3 74 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 259
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 72 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 259 (accept_3_3 71 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 259 (Polychromatic418967fa.accept_13_5_2_12_1_1301 70 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 259 (accept_3_3 68 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 67 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 259
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 66 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 259 (accept_3_3 65 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 259 (accept_3_3 62 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 259
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 60 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 106 259 (accept_3_3 59 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 106 259 (Polychromatic418967fa.accept_13_6_2_12_1_2802 58 106 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 259 (accept_3_3 56 106 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 259 (Polychromatic418967fa.accept_10_5_6_9_1_2235
  55 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 259
  (Polychromatic418967fa.accept_20_14_6_19_1_10095 54 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 106 259 (accept_3_3 53 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 106 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 106 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 106 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 106 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 259 (accept_3_3 50 106 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 259
  (Polychromatic418967fa.accept_14_6_8_7_1_589 48 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 259 (accept_3_3 47 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 259 (Polychromatic418967fa.accept_19_8_11_12_1_6165 46 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 259 (accept_3_3 44 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 259
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 42 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 259 (accept_3_3 41 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 259 (accept_3_3 38 106 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 259
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 106 259 (accept_3_3 35 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 106 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 34 106 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 259 (accept_3_3 32 106 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 259
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 106 259 (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 106 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 106 259 (accept_3_3 29 106 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 106 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 106 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 106 259 (accept_3_3 26 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 106 259 (Polychromatic418967fa.accept_19_5_11_12_1_11765 24 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 106 259 (accept_3_3 23 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 106 259 (Polychromatic418967fa.accept_18_4_16_7_1_1873 22 106
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 106 259 (accept_3_3 20 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 106 259 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 106 259 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 106 259 (accept_3_3 17 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 106 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 106
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 106 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 106 259 (accept_3_3 14 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 106 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 106 259 (accept_3_3 11 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 106 259 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 106
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 106 259 (accept_3_3 8 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  106 259 (Polychromatic418967fa.accept_16_7_10_3_1_2210 7 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 106 259 (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 106 259 (accept_3_3 5 106 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 106 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 106 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 106 259 (accept_3_3 2 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  106 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 106
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 259 (allA_succ_of_accept 104 105 259 (accept_3_3 104 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 103 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 105
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 259 (accept_3_3 101 105
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 259
  (Polychromatic418967fa.accept_6_4_3_1_1_57 100 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 99 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 105 259 7 14 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 105 259
  (Polychromatic418967fa.accept_19_2_10_12_1_3446 97 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 105 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 96 105 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 259 (accept_3_3 95 105 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 105 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 105 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 93 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 105 259 (accept_3_3 92 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91
  105 259 7 13 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 90 105 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 259 (accept_3_3 89 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 105 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 105 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 105 259 (Polychromatic418967fa.accept_12_3_9_7_1_472
  87 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 259 (accept_3_3 86
  105 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 259
  (Polychromatic418967fa.accept_9_4_6_7_1_286 85 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 105 259 7 12 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 105 259 (accept_3_3 83 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 105 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 105
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 259 (accept_3_3 80 105
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 259
  (Polychromatic418967fa.accept_19_3_10_12_1_6217 79 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 105 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 105 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 105 259 7 11 15 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 105 259
  (Polychromatic418967fa.accept_6_4_3_1_1_57 76 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 105 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 259 (accept_3_3 74 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 105 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 105 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 259
  (Polychromatic418967fa.accept_26_20_1_25_1_15779 72 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 105 259 (accept_3_3 71 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 105 259 7 10 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 105 259 (Polychromatic418967fa.accept_26_17_1_25_1_13915 69 105 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 259 (accept_3_3 68 105 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 105 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 259 (accept_3_3 65 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 105 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 105 259 7 9 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 105 259 (accept_3_3 62 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 259 (Polychromatic418967fa.accept_13_8_1_12_1_762 60 105
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 259 (accept_3_3 59 105
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 105 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 105 259 7 8 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 105 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 55
  105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 259 (accept_3_3 53 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 105 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 259 (accept_3_3 50 105 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 105 259 7 7 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 105 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 48
  105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 259 (accept_3_3 47
  105 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 105 259 (Polychromatic418967fa.accept_27_18_24_16_1_15778 45 105 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 259 (accept_3_3 44 105 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 259 (Polychromatic418967fa.accept_23_20_13_6_1_15777 43 105 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 259 7 6 15 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 259 (accept_3_3 41
  105 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 259
  (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 105 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 259 (accept_3_3 38 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 105 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 105 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233
  36 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 259 7 5 15 37
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 105 259 (Polychromatic418967fa.accept_17_16_3_4_1_6010 33 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 259 (accept_3_3 32 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 105 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 105 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 259 (accept_3_3 29
  105 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 105 259 7 4 15 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 105 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 105 259 (accept_3_3 26 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 105 259 (Polychromatic418967fa.accept_19_6_10_12_1_11771 25 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 105 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 259 (accept_3_3 23 105 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 259 7 3 15 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 259 (accept_3_3 20
  105 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 259
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 259 (accept_3_3 17 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 105 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 259 (Polychromatic418967fa.accept_12_3_9_7_1_472
  15 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 105 259 7 2 15 37
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 105 259
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 259 (accept_3_3 11 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 105 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 259
  (Polychromatic418967fa.accept_19_9_10_12_1_6161 9 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 259 (accept_3_3 8 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 105
  259 7 1 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  105 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 259 (accept_3_3 5 105 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 105 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 259 (accept_3_3 2 105 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  105 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 259 (allA_of_3_1 104 104 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 259
  (allA_succ_of_accept 102 103 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 102 103 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 259 (accept_3_3 101 103 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 100 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 259
  (Polychromatic418967fa.accept_15_9_13_4_1_1209 99 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 259 (accept_3_3 98 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 259 (Polychromatic418967fa.accept_21_13_19_7_1_5162 97 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 259 (accept_3_3 95 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 94 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 93 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 259 (accept_3_3 92 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 259 (Polychromatic418967fa.accept_11_2_4_6_1_2412 90 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 259 (accept_3_3 89 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 259 (Polychromatic418967fa.accept_21_4_19_7_1_5142 88 103
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 87 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 259 (accept_3_3 86 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 85 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 259 (accept_3_3 83 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 259
  (Polychromatic418967fa.accept_15_6_13_4_1_2040 81 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 259 (accept_3_3 80 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 259 (Polychromatic418967fa.accept_11_2_4_6_1_2412 79 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 78 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 259 (accept_3_3 77 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 76 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 259 (accept_3_3 74 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 259 (Polychromatic418967fa.accept_14_2_5_7_1_3767 72 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 259 (accept_3_3 71 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 70 103
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 69 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 259 (accept_3_3 68 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 259 (Polychromatic418967fa.accept_19_10_8_12_1_7733 67 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 259 (accept_3_3 65 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 259
  (Polychromatic418967fa.accept_16_15_7_3_1_4273 63 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 259 (accept_3_3 62 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 259 (Polychromatic418967fa.accept_19_4_8_12_1_4757 61 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 259 (accept_3_3 59 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 259 (Polychromatic418967fa.accept_14_2_5_7_1_3767 58 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 259 (accept_3_3 56 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 259 (accept_3_3 53 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 103 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 51 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 259 (accept_3_3 50 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 259 (Polychromatic418967fa.accept_19_11_8_12_1_6204 49 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 259 (accept_3_3 47 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 259
  (Polychromatic418967fa.accept_19_7_8_12_1_9107 45 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 259 (accept_3_3 44 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 259 (Polychromatic418967fa.accept_16_11_7_3_1_3163 43 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 259 (accept_3_3 41 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 259 (Polychromatic418967fa.accept_14_12_5_7_1_2010 40 103 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 259 (accept_3_3 38 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 259 (accept_3_3 35 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 34 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 259 (accept_3_3 32 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 259 (Polychromatic418967fa.accept_16_15_7_3_1_4273 31 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 259 (accept_3_3 29 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 259
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 259 (accept_3_3 26 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 259 (accept_3_3 23 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 259 (Polychromatic418967fa.accept_17_5_1_4_1_3460 22 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 259 (accept_3_3 20 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 259 (Polychromatic418967fa.accept_21_18_19_7_1_5165 18 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 259 (accept_3_3 17 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 259 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 103
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 259 (accept_3_3 14 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 259 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 259 (accept_3_3 11 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 259
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 259 (accept_3_3 8 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 259 (Polychromatic418967fa.accept_19_7_8_12_1_9107 7 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 259 (accept_3_3 5 103 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 103 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 259 (accept_3_3 2 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 103 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 259 (allA_succ_of_accept 101 102 259 (accept_3_3 101 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 102 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 100 102 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 102 259 (Polychromatic418967fa.accept_15_9_12_4_1_2023 99 102
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 259 (accept_3_3 98 102
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 259 (Polychromatic418967fa.accept_4_1_2_3_1_9
  97 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 96 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 259 (accept_3_3 95 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 102 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 94 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 259 (accept_3_3 92 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 91 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 259
  (Polychromatic418967fa.accept_19_14_7_12_1_7732 90 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 102 259 (accept_3_3 89 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 102 259 (Polychromatic418967fa.accept_13_10_11_12_1_1320 88 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 102 259 (Polychromatic418967fa.accept_9_6_3_7_1_580
  87 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 259 (accept_3_3 86
  102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 85 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 102 259 (Polychromatic418967fa.accept_15_9_12_4_1_2023 84 102 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 102 259 (accept_3_3 83 102 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 102 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 102 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 81
  102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 259 (accept_3_3 80
  102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 259
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 79 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 102 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 78 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 102 259 (accept_3_3 77 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 102 259
  (Polychromatic418967fa.accept_11_9_3_6_1_797 75 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 102 259 (accept_3_3 74 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 102 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 102 259 (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 102 259 (accept_3_3 71 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 259 (Polychromatic418967fa.accept_25_20_2_9_1_15776 70 102
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 102 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 102 259 (accept_3_3 68 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 102 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 102 259 (Polychromatic418967fa.accept_13_1_11_12_1_1322 66 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 102 259 (accept_3_3 65 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 102 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 102 259
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 102 259 (accept_3_3 62 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 102 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 102 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 102 259 (accept_3_3 59 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 102 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 102 259 (accept_3_3 56 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 102 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 102 259 (Polychromatic418967fa.accept_15_9_12_4_1_2023 54 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 102 259 (accept_3_3 53 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 259 (Polychromatic418967fa.accept_11_8_3_6_1_1855 52 102
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 102 259 (accept_3_3 50 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 102 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 102 259 (Polychromatic418967fa.accept_21_6_18_7_1_3764 48 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 102 259 (accept_3_3 47 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 102 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 102 259 (accept_3_3 44 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 102 259 (Polychromatic418967fa.accept_13_4_11_12_1_1318 43 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 102 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 102 259 (accept_3_3 41 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 259
  (Polychromatic418967fa.accept_14_11_4_7_1_609 39 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 102 259 (accept_3_3 38 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 102 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 102 259 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 259 (accept_3_3 35 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 259 (Polychromatic418967fa.accept_16_2_6_3_1_5396 34 102
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 102 259 (accept_3_3 32 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 102 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 102 259 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 259 (accept_3_3 29 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 102 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 259
  (Polychromatic418967fa.accept_10_7_2_9_1_775 27 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 102 259 (accept_3_3 26 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 102 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 102 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 259 (accept_3_3 23 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 102 259 (accept_3_3 20 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 102 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 102 259 (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 259 (accept_3_3 17 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 259 (Polychromatic418967fa.accept_15_1_12_4_1_2022 16 102
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 102 259 (accept_3_3 14 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 102 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 102 259 (Polychromatic418967fa.accept_20_12_2_19_1_4286 12 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 259 (accept_3_3 11 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 102 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 102 259 (accept_3_3 8 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  102 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 102 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 259 (accept_3_3 5 102 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 102 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 259
  (Polychromatic418967fa.accept_14_3_4_7_1_175 3 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 102 259 (accept_3_3 2 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  102 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 102
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 259 (allA_of_3_1 101 101 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 259 (allA_succ_of_accept 99
  100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 100 259 (accept_3_3 98 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 100 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 97 100 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 100 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 100 259 (accept_3_3 95 100 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 100 259 (Polychromatic418967fa.accept_9_4_1_7_1_293
  94 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 100 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 100 259 (accept_3_3 92 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 100 259 (Polychromatic418967fa.accept_19_15_5_12_1_13123 91 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 100 259 (Polychromatic418967fa.accept_21_6_16_7_1_3714 90 100 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 100 259 (accept_3_3 89 100 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 100 259
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 88 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 100 259 (accept_3_3 86 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 100 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 100 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 100 259 (accept_3_3 83 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 100 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 82 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 100 259 (accept_3_3 80 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 100 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 100 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 78 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 100 259 (accept_3_3 77 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 100 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 100 259 (accept_3_3 74 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 100 259 (Polychromatic418967fa.accept_11_7_1_6_1_1281 73 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 100 259
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 72 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 100 259 (accept_3_3 71 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 100 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 100 259 (accept_3_3 68 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 100 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 100 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 100 259 (accept_3_3 65 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 100 259 (Polychromatic418967fa.accept_19_7_5_12_1_7756 64 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 100 259 (accept_3_3 62 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 100 259 (Polychromatic418967fa.accept_14_5_2_7_1_2804 61 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 100 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 100 259 (accept_3_3 59 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 100 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 100 259 (accept_3_3 56 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 100 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 100 259
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 54 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 100 259 (accept_3_3 53 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 100 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 52 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 100 259 (accept_3_3 50 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 100 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 100 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 100 259 (accept_3_3 47 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 100 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 100 259 (accept_3_3 44 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 259 (Polychromatic418967fa.accept_15_13_10_4_1_1232 43 100 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 100 259 (accept_3_3 41 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 100 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 100 259 (accept_3_3 38 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 100 259 (Polychromatic418967fa.accept_14_9_2_7_1_1242 37 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 259
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 100 259 (accept_3_3 35 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 100 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 100 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 259 (accept_3_3 32 100 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 100 259 (Polychromatic418967fa.accept_8_7_4_3_1_156
  31 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 100 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 100 259 (accept_3_3 29 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 100 259 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 259 (accept_3_3 26 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 100 259 (Polychromatic418967fa.accept_21_4_16_7_1_11401 25 100 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 100 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 100 259 (accept_3_3 23 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 100 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 100 259 (accept_3_3 20 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 100 259 (Polychromatic418967fa.accept_14_5_2_7_1_2804 19 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 259
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 100 259 (accept_3_3 17 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 100 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 100 259 (accept_3_3 14 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 100 259 (accept_3_3 11 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 100 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 259 (accept_3_3 8 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 100 259 (accept_3_3 5 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  100 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 100 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 100 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 259 (accept_3_3 2 100 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 259 (Polychromatic418967fa.accept_16_1_4_3_1_3148 1 100 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  259 (allA_succ_of_accept 98 99 259 (accept_3_3 98 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 259 (Polychromatic418967fa.accept_14_13_1_7_1_1211 97 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 259 (Polychromatic418967fa.accept_13_5_8_12_1_2759 96 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 259 (accept_3_3 95 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 93 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 259 (accept_3_3 92 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 259 (Polychromatic418967fa.accept_23_22_7_6_1_5838 91 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 259 (Polychromatic418967fa.accept_14_6_1_7_1_2775 90 99 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 259 (accept_3_3 89 99 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 259
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 87 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 259 (accept_3_3 86 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 259 (Polychromatic418967fa.accept_13_7_8_12_1_2810 85 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 259 (Polychromatic418967fa.accept_19_8_4_12_1_4768 84 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 259 (accept_3_3 83 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 259 (accept_3_3 80 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 259 (Polychromatic418967fa.accept_13_1_8_12_1_2045 79 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 259 (Polychromatic418967fa.accept_14_8_1_7_1_3725 78 99 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 259 (accept_3_3 77 99 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 259
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 75 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 259 (accept_3_3 74 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 259 (Polychromatic418967fa.accept_15_13_9_4_1_3892 73 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 259 (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 259 (accept_3_3 71 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 69 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 259 (accept_3_3 68 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 259 (Polychromatic418967fa.accept_27_13_18_16_1_15775 67 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 259 (Polychromatic418967fa.accept_13_1_8_12_1_2045 66 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 259 (accept_3_3 65 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 259
  (Polychromatic418967fa.accept_19_6_4_12_1_6193 63 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 259 (accept_3_3 62 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 259 (Polychromatic418967fa.accept_13_9_8_12_1_2031 61 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 259 (Polychromatic418967fa.accept_17_9_14_4_1_3483 60 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 259 (accept_3_3 59 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 259 (accept_3_3 56 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 259 (Polychromatic418967fa.accept_14_13_1_7_1_1211 55 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 259 (Polychromatic418967fa.accept_19_16_4_12_1_6248 54 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 259 (accept_3_3 53 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 259
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 51 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 259 (accept_3_3 50 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 259 (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 259 (Polychromatic418967fa.accept_13_9_8_12_1_2031 48 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 259 (accept_3_3 47 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 259 (accept_3_3 44 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 259 (Polychromatic418967fa.accept_13_4_8_12_1_3526 43 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 259 (Polychromatic418967fa.accept_15_12_9_4_1_3898 42 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 259 (accept_3_3 41 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 259
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 39 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 259 (accept_3_3 38 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 259 (Polychromatic418967fa.accept_22_15_11_17_1_15774 37 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 259 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 259 (accept_3_3 35 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 259 (accept_3_3 32 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 259 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 259 (Polychromatic418967fa.accept_13_4_8_12_1_3526 30 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 259 (accept_3_3 29 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 259
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 259 (accept_3_3 26 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 259 (Polychromatic418967fa.accept_15_10_9_4_1_2924 25 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 259 (Polychromatic418967fa.accept_17_7_14_4_1_4745 24 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 259 (accept_3_3 23 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 259 (accept_3_3 20 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 259 (Polychromatic418967fa.accept_21_19_15_7_1_3709 19 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 259 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 259 (accept_3_3 17 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 259
  (Polychromatic418967fa.accept_22_15_11_17_1_15774 15 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 259 (accept_3_3 14 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 259 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 99 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 259 (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 99
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 259 (accept_3_3 11 99 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10
  99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 259 (accept_3_3 8 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  259 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 259 (Polychromatic418967fa.accept_14_6_1_7_1_2775 6 99 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 259 (accept_3_3 5 99 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 259
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 3 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 259 (accept_3_3 2 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  259 (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 99 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  259 (allA_of_3_1 98 98 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 259 (allA_succ_of_accept 96 97 259
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 96 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 259 (accept_3_3 95 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 259 (Polychromatic418967fa.accept_13_2_6_12_1_1334 93 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 259 (accept_3_3 92 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 91 97 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 259 (accept_3_3 89 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 259 (Polychromatic418967fa.accept_10_8_7_9_1_425 88 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 259 (Polychromatic418967fa.accept_15_12_7_4_1_2921 87 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 259 (accept_3_3 86 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 259 (Polychromatic418967fa.accept_13_7_6_12_1_2027 85 97
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 259
  (Polychromatic418967fa.accept_16_4_1_3_1_6581 84 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 259 (accept_3_3 83 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 259 (Polychromatic418967fa.accept_21_18_13_7_1_9883 81 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 259 (accept_3_3 80 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 259 (Polychromatic418967fa.accept_19_3_2_12_1_13118 79 97
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 259 (accept_3_3 77 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 259 (Polychromatic418967fa.accept_14_6_13_7_1_2015 76 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 259 (Polychromatic418967fa.accept_13_10_6_12_1_2780 75 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 259 (accept_3_3 74 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 259 (Polychromatic418967fa.accept_21_10_13_7_1_6789 73 97
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 259
  (Polychromatic418967fa.accept_10_2_7_9_1_783 72 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 259 (accept_3_3 71 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 69 97 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 259 (accept_3_3 68 97 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 259 (Polychromatic418967fa.accept_13_2_6_12_1_1334 67 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 259 (accept_3_3 65 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 259 (Polychromatic418967fa.accept_14_8_13_7_1_2798 64 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 259 (Polychromatic418967fa.accept_15_3_7_4_1_1225 63 97 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 259 (accept_3_3 62 97 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 259 (Polychromatic418967fa.accept_16_13_1_3_1_2205 61 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 259
  (Polychromatic418967fa.accept_17_9_12_4_1_3468 60 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 259 (accept_3_3 59 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 259 (Polychromatic418967fa.accept_13_5_6_12_1_2750 57 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 259 (accept_3_3 56 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 259 (Polychromatic418967fa.accept_15_10_7_4_1_1222 55 97
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 259 (accept_3_3 53 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 259 (Polychromatic418967fa.accept_10_2_7_9_1_783 52 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 259 (Polychromatic418967fa.accept_21_9_13_7_1_5154 51 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 259 (accept_3_3 50 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 259 (Polychromatic418967fa.accept_13_10_6_12_1_2780 49 97
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 259
  (Polychromatic418967fa.accept_10_8_7_9_1_425 48 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 259 (accept_3_3 47 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 259 (Polychromatic418967fa.accept_16_13_1_3_1_2205 45 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 259 (accept_3_3 44 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 259 (Polychromatic418967fa.accept_14_1_13_7_1_1205 43 97
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 259 (accept_3_3 41 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 259 (Polychromatic418967fa.accept_15_10_7_4_1_1222 40 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 259 (Polychromatic418967fa.accept_19_1_2_12_1_7725 39 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 259 (accept_3_3 38 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 259 (Polychromatic418967fa.accept_21_16_13_7_1_8385 37 97
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 259
  (Polychromatic418967fa.accept_11_3_9_6_1_105 36 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 259 (accept_3_3 35 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 259 (Polychromatic418967fa.accept_13_7_6_12_1_2027 33 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 259 (accept_3_3 32 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 259 (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 97
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 259 (accept_3_3 29 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 259 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 259 (Polychromatic418967fa.accept_15_12_7_4_1_2921 27 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 259 (accept_3_3 26 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 97 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 259
  (Polychromatic418967fa.accept_17_7_12_4_1_2524 24 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 259 (accept_3_3 23 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 259 (Polychromatic418967fa.accept_28_21_13_7_1_15773 21 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 259 (accept_3_3 20 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 259 (Polychromatic418967fa.accept_17_2_12_4_1_5987 19 97
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 259 (accept_3_3 17 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 259 (Polychromatic418967fa.accept_20_16_17_19_1_8721 16 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 259 (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 259 (accept_3_3 14 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 259 (Polychromatic418967fa.accept_16_13_1_3_1_2205 13 97
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 259
  (Polychromatic418967fa.accept_10_2_7_9_1_783 12 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 259 (accept_3_3 11 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 259 (Polychromatic418967fa.accept_17_9_12_4_1_3468 9 97 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 259 (accept_3_3 8 97 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 259 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 259 (accept_3_3 5 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  259 (Polychromatic418967fa.accept_16_4_1_3_1_6581 4 97 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 97 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 97 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 259 (accept_3_3 2 97 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 259 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 97 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 259
  (allA_succ_of_accept 95 96 259 (accept_3_3 95 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  96 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 94 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 96 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 96 259 (accept_3_3 92 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 259
  (Polychromatic418967fa.accept_20_10_16_19_1_5674 90 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 96 259 (accept_3_3 89 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 259 (Polychromatic418967fa.accept_15_13_6_4_1_1221 88 96 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 96 259 (Polychromatic418967fa.accept_19_11_1_12_1_6237 87 96
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 259 (accept_3_3 86 96 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 85
  96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 259 (accept_3_3 83 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  96 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 259 (Polychromatic418967fa.accept_18_9_6_7_1_6719 81 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 259 (accept_3_3 80 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 259 (Polychromatic418967fa.accept_13_1_5_12_1_306 79 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 259
  (Polychromatic418967fa.accept_17_10_11_4_1_2522 78 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 96 259 (accept_3_3 77 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  96 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 96 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 259 (accept_3_3 74 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 259
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 72 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 259 (accept_3_3 71 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  96 259 (Polychromatic418967fa.accept_15_10_6_4_1_1256 70 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 259 (Polychromatic418967fa.accept_11_3_8_6_1_788 69 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 259 (accept_3_3 68 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 259 (accept_3_3 65 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 259 (accept_3_3 62 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 259 (Polychromatic418967fa.accept_14_5_12_7_1_2767 61 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 259
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 60 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 259 (accept_3_3 59 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 259 (accept_3_3 56 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 259
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 54 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 259 (accept_3_3 53 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 259 (Polychromatic418967fa.accept_25_2_21_9_1_15772 52 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 259 (Polychromatic418967fa.accept_14_9_12_7_1_597 51 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 259 (accept_3_3 50 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 259 (accept_3_3 47 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 259 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 259 (accept_3_3 44 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 259
  (Polychromatic418967fa.accept_19_4_1_12_1_4803 42 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 259 (accept_3_3 41 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 259 (accept_3_3 38 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 259
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 259 (accept_3_3 35 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 259 (Polychromatic418967fa.accept_13_8_5_12_1_2755 34 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 259 (accept_3_3 32 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 259 (accept_3_3 29 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 259 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 259 (accept_3_3 26 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 259 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 259
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 259 (accept_3_3 23 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 259 (accept_3_3 20 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 259
  (Polychromatic418967fa.accept_19_18_1_12_1_6235 18 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 259 (accept_3_3 17 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 259 (Polychromatic418967fa.accept_14_2_12_7_1_617 16 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 259 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 259 (accept_3_3 14 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 259 (accept_3_3 11 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 259 (Polychromatic418967fa.accept_14_9_12_7_1_597 9 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 259 (accept_3_3 8 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 259 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 96 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 259
  (Polychromatic418967fa.accept_13_6_5_12_1_307 6 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 259 (accept_3_3 5 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  259 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 96 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 259 (accept_3_3 2 96 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 96 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 259
  (allA_of_3_1 95 95 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 259 (allA_succ_of_accept 93 94 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 94 259 (accept_3_3 92 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  94 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 94 259 (Polychromatic418967fa.accept_22_2_6_17_1_4686 90 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 259 (accept_3_3 89 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 88 94 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 94 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 94 259 (accept_3_3 86 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  94 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 94 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 259 (accept_3_3 83 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 259 (accept_3_3 80 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 259 (Polychromatic418967fa.accept_21_16_10_7_1_3782 79 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 78 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 259 (accept_3_3 77 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 259 (accept_3_3 74 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 259 (Polychromatic418967fa.accept_19_15_18_12_1_6180 72 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 259 (accept_3_3 71 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 259 (Polychromatic418967fa.accept_17_2_9_4_1_3463 70 94 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 259 (accept_3_3 68 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 259 (Polychromatic418967fa.accept_13_2_3_12_1_735 67 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 259 (accept_3_3 65 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 259 (accept_3_3 62 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 259 (accept_3_3 59 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 259 (accept_3_3 56 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 259 (Polychromatic418967fa.accept_13_2_3_12_1_735 54 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 259 (accept_3_3 53 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 259 (accept_3_3 50 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 259 (accept_3_3 47 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 259 (accept_3_3 44 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 259 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 259 (accept_3_3 41 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 259 (accept_3_3 38 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 259 (Polychromatic418967fa.accept_17_2_9_4_1_3463 36 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 259 (accept_3_3 35 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 259 (Polychromatic418967fa.accept_18_16_4_7_1_2927 34 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 259 (accept_3_3 32 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 259 (Polychromatic418967fa.accept_14_3_10_7_1_3773 31 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 259 (accept_3_3 29 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 259 (accept_3_3 26 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 259 (accept_3_3 23 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 259 (Polychromatic418967fa.accept_13_9_3_12_1_2025 22 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 259 (accept_3_3 20 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 259 (accept_3_3 17 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 259 (accept_3_3 14 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 259 (accept_3_3 11 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 259 (accept_3_3 8 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  259 (Polychromatic418967fa.accept_19_7_18_12_1_3427 7 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 94 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 259 (accept_3_3 5 94 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 94 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 94 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 94 259 (accept_3_3 2 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94
  259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 93 259 (allA_succ_of_accept 92 93 259 (accept_3_3 92 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 91 93 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 93 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 259 (accept_3_3 89 93 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 88
  93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 87 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 259 (accept_3_3 86 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 85 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 84 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 259 (accept_3_3 83 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 259
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 81 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 259 (accept_3_3 80 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 259 (Polychromatic418967fa.accept_13_1_2_12_1_1299 79 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 259 (accept_3_3 77 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 75 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 259 (accept_3_3 74 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 259 (Polychromatic418967fa.accept_14_2_9_7_1_5633 72 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 259 (accept_3_3 71 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 69 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 259 (accept_3_3 68 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 259 (accept_3_3 65 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 259 (accept_3_3 62 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 259 (Polychromatic418967fa.accept_14_5_9_7_1_590 61 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 259 (accept_3_3 59 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 259
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 57 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 259 (accept_3_3 56 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 259 (accept_3_3 53 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 259 (accept_3_3 50 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 259 (Polychromatic418967fa.accept_18_12_3_7_1_5373 48 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 259 (accept_3_3 47 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 259
  (Polychromatic418967fa.accept_11_1_5_6_1_397 45 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 259 (accept_3_3 44 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 259 (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 259 (accept_3_3 41 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 259 (accept_3_3 38 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 259 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 259 (accept_3_3 35 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 259 (accept_3_3 32 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 259 (accept_3_3 29 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 259 (accept_3_3 26 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 259 (Polychromatic418967fa.accept_19_6_17_12_1_10550 25 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 259 (accept_3_3 23 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 259
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 259 (accept_3_3 20 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 259 (accept_3_3 17 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 259 (accept_3_3 14 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 259 (accept_3_3 11 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 259
  (Polychromatic418967fa.accept_18_9_3_7_1_9449 9 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 259 (accept_3_3 8 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  259 (Polychromatic418967fa.accept_15_7_3_4_1_574 7 93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 259 (accept_3_3 5 93 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 3
  93 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 259 (accept_3_3 2 93 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 93
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 259
  (allA_of_3_1 92 92 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 259 (allA_succ_of_accept 90 91 259
  (Polychromatic418967fa.accept_17_5_6_4_1_8607 90 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 259 (accept_3_3 89 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 259 (Polychromatic418967fa.accept_10_8_1_9_1_413 88 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 87 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 259 (accept_3_3 86 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 91 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 91 259 7 12 13 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 91 259 (accept_3_3 83 91 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 91 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248
  82 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 259
  (Polychromatic418967fa.accept_19_5_15_12_1_6273 81 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 91 259 (accept_3_3 80 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  91 259 (Polychromatic418967fa.accept_16_15_11_3_1_2179 79 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 91 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 91 259 7 11 13 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 91 259
  (Polychromatic418967fa.accept_9_4_1_7_1_293 76 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 91 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 91 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 259 (accept_3_3 74 91 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 91 259 (Polychromatic418967fa.accept_17_5_6_4_1_8607 73 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248
  72 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 259 (accept_3_3 71
  91 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 91 259 7 10 13 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 91 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 69 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 259 (accept_3_3 68 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 259 (accept_3_3 65 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 259 (Polychromatic418967fa.accept_11_9_3_6_1_797 64 91 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 91 259 7 9 13 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 91 259 (accept_3_3 62 91 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 259 (Polychromatic418967fa.accept_17_10_6_4_1_2506 61 91
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 259 (accept_3_3 59 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 91 259 7 8 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 91 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 55
  91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 259
  (Polychromatic418967fa.accept_16_6_11_3_1_2198 54 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 259 (accept_3_3 53 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 52 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 259 (accept_3_3 50 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 49 91 259 7 7 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 48 91 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 91 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 259 (accept_3_3 47 91 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 259 (Polychromatic418967fa.accept_16_14_11_3_1_4249 46 91
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 259
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 259 (accept_3_3 44 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 259 (Polychromatic418967fa.accept_19_5_15_12_1_6273 43 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 91 259 7 6 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 91 259 (accept_3_3 41 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 91 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 91 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 259 (accept_3_3 38 91 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 259
  (Polychromatic418967fa.accept_19_18_15_12_1_11773 37 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 259 (Polychromatic418967fa.accept_17_2_6_4_1_2431 36 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 91 259 7 5 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 91 259 (Polychromatic418967fa.accept_18_16_1_7_1_4083
  34 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 259 (accept_3_3 32 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 259 (accept_3_3 29 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 91 259 7 4 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 91 259 (Polychromatic418967fa.accept_15_12_1_4_1_2899 27 91 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 259 (accept_3_3 26 91 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 91 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 259 (accept_3_3 23 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 91 259 7 3 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 91 259 (accept_3_3 20 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 91 259 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 91 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 259 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 91 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 259 (accept_3_3 17 91 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 259 (Polychromatic418967fa.accept_18_16_1_7_1_4083
  16 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 91 259 7 2 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 91 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 91 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 259 (accept_3_3 11 91 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 259 (Polychromatic418967fa.accept_17_10_6_4_1_2506
  10 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 259
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 259 (accept_3_3 8 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 259
  7 1 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 91
  259 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 259 (accept_3_3 5 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 91 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 259 (accept_3_3 2 91 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 259 (Polychromatic418967fa.accept_23_1_22_6_1_15771 1 91 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 259
  (allA_succ_of_accept 89 90 259 (accept_3_3 89 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  90 259 (Polychromatic418967fa.accept_21_4_6_7_1_3693 88 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 259 (Polychromatic418967fa.accept_16_7_10_3_1_2210 87 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 259 (accept_3_3 86 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 90 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 259
  (Polychromatic418967fa.accept_17_16_5_4_1_2499 84 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 259 (accept_3_3 83 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  90 259 (Polychromatic418967fa.accept_19_6_14_12_1_4811 82 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 90 259 (accept_3_3 80 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 259 (Polychromatic418967fa.accept_21_16_6_7_1_6764 79 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 259
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 78 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 90 259 (accept_3_3 77 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  90 259 (Polychromatic418967fa.accept_16_12_10_3_1_4209 76 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 90 259 (Polychromatic418967fa.accept_20_15_10_19_1_10068 75 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 259 (accept_3_3 74 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 259
  (Polychromatic418967fa.accept_21_9_6_7_1_6749 72 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 90 259 (accept_3_3 71 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  90 259 (Polychromatic418967fa.accept_11_4_2_6_1_389 70 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 259 (accept_3_3 68 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 259 (Polychromatic418967fa.accept_17_16_5_4_1_2499 67 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 259
  (Polychromatic418967fa.accept_19_9_14_12_1_7764 66 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 90 259 (accept_3_3 65 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  90 259 (Polychromatic418967fa.accept_14_8_6_7_1_1934 64 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 90 259 (Polychromatic418967fa.accept_19_6_14_12_1_4811 63 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 259 (accept_3_3 62 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 259
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 60 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 90 259 (accept_3_3 59 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  90 259 (Polychromatic418967fa.accept_21_16_6_7_1_6764 58 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 259 (accept_3_3 56 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 259 (Polychromatic418967fa.accept_14_13_6_7_1_2013 55 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 259
  (Polychromatic418967fa.accept_19_16_14_12_1_6261 54 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 90 259 (accept_3_3 53 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 259 (Polychromatic418967fa.accept_17_1_5_4_1_8532 52 90 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 259 (Polychromatic418967fa.accept_19_13_14_12_1_4797 51 90
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 259 (accept_3_3 50 90 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 259
  (Polychromatic418967fa.accept_11_4_2_6_1_389 48 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 90 259 (accept_3_3 47 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  90 259 (Polychromatic418967fa.accept_20_6_10_19_1_15770 46 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 259 (accept_3_3 44 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 259 (Polychromatic418967fa.accept_14_1_6_7_1_1936 43 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 259
  (Polychromatic418967fa.accept_25_17_15_9_1_12246 42 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 90 259 (accept_3_3 41 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 259 (Polychromatic418967fa.accept_17_6_5_4_1_7238 40 90 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 259 (Polychromatic418967fa.accept_16_7_10_3_1_2210 39 90
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 259 (accept_3_3 38 90 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 259
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 259 (accept_3_3 35 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  90 259 (Polychromatic418967fa.accept_21_13_6_7_1_1237 34 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 259 (accept_3_3 32 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 259 (Polychromatic418967fa.accept_20_11_10_19_1_8714 31 90 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 259
  (Polychromatic418967fa.accept_21_9_6_7_1_6749 30 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 259 (accept_3_3 29 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 259 (Polychromatic418967fa.accept_16_12_10_3_1_4209 28 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 259 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 259 (accept_3_3 26 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 259
  (Polychromatic418967fa.accept_21_3_6_7_1_6750 24 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 259 (accept_3_3 23 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  90 259 (Polychromatic418967fa.accept_14_8_6_7_1_1934 22 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 259 (accept_3_3 20 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 259 (Polychromatic418967fa.accept_22_19_2_17_1_15769 19 90 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 259
  (Polychromatic418967fa.accept_17_1_5_4_1_8532 18 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 90 259 (accept_3_3 17 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  90 259 (Polychromatic418967fa.accept_17_16_5_4_1_2499 16 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 90 259 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 259 (accept_3_3 14 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 259
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 12 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 259 (accept_3_3 11 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 259 (Polychromatic418967fa.accept_19_10_14_12_1_4795 10 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 259 (accept_3_3 8 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 259 (Polychromatic418967fa.accept_16_7_10_3_1_2210 7 90 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 259
  (Polychromatic418967fa.accept_17_6_5_4_1_7238 6 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 259 (accept_3_3 5 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  259 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 90 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 90 259 (Polychromatic418967fa.accept_20_3_10_19_1_5640 3 90 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 259 (accept_3_3 2 90 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 90 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 259
  (allA_of_3_1 89 89 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 259 (allA_succ_of_accept 87 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 88 259 (accept_3_3 86 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  88 259 (Polychromatic418967fa.accept_13_7_10_12_1_2047 85 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 88 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 84 88 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 259 (accept_3_3 83 88 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 88 259 (accept_3_3 80 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  88 259 (Polychromatic418967fa.accept_21_16_4_7_1_5191 79 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 88 259 (Polychromatic418967fa.accept_23_9_19_6_1_7606 78 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 259 (accept_3_3 77 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 259 (Polychromatic418967fa.accept_13_11_10_12_1_1338 76 88
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 259 (accept_3_3 74 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 259 (Polychromatic418967fa.accept_13_8_10_12_1_1337 73 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 259 (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 259 (accept_3_3 71 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 88 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 259 (accept_3_3 68 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 67 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 88 259 (Polychromatic418967fa.accept_14_10_4_7_1_1214 66 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 259 (accept_3_3 65 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 64 88 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 88 259 (accept_3_3 62 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  88 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 61 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 88 259 (Polychromatic418967fa.accept_13_8_10_12_1_1337 60 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 259 (accept_3_3 59 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 88 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 259 (accept_3_3 56 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 55 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 88 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 259 (accept_3_3 53 88 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 259 (Polychromatic418967fa.accept_14_10_4_7_1_1214 52 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 259 (accept_3_3 50 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 259 (Polychromatic418967fa.accept_20_9_8_19_1_802 49 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 259 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 259 (accept_3_3 47 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 88 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 259 (accept_3_3 44 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 259 (Polychromatic418967fa.accept_16_11_8_3_1_3183 43 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 259 (Polychromatic418967fa.accept_24_18_16_19_1_15768 42 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 259 (accept_3_3 41 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 40 88
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 259 (accept_3_3 38 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 37 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 259 (Polychromatic418967fa.accept_15_6_13_4_1_2040 36 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 259 (accept_3_3 35 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 88 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 259 (accept_3_3 32 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 259 (Polychromatic418967fa.accept_17_13_3_4_1_2537 30 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 259 (accept_3_3 29 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 259 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 88
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 259 (accept_3_3 26 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 259 (Polychromatic418967fa.accept_14_11_4_7_1_609 25 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 88 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 259 (accept_3_3 23 88 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 259 (accept_3_3 20 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 259 (Polychromatic418967fa.accept_13_6_10_12_1_2049 19 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 259 (Polychromatic418967fa.accept_21_18_4_7_1_8346 18 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 259 (accept_3_3 17 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 259 (Polychromatic418967fa.accept_17_16_3_4_1_6010 16 88
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 259 (accept_3_3 14 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 259 (Polychromatic418967fa.accept_16_13_8_3_1_5374 13 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 259 (Polychromatic418967fa.accept_16_12_8_3_1_4241 12 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 259 (accept_3_3 11 88 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 88 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 259 (accept_3_3 8 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  259 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 88 259 (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 88 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 259 (accept_3_3 5 88 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 88 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 88 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 259 (accept_3_3 2 88 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 1
  88 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 259
  (allA_succ_of_accept 86 87 259 (accept_3_3 86 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  87 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 85 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 259 (accept_3_3 83 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 259 (accept_3_3 80 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 259 (Polychromatic418967fa.accept_16_15_7_3_1_4273 79 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 259 (Polychromatic418967fa.accept_10_8_7_9_1_425 78 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 259 (accept_3_3 77 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 75 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 259 (accept_3_3 74 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 259 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 259 (accept_3_3 71 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 69 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 259 (accept_3_3 68 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 259 (accept_3_3 65 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 259
  (Polychromatic418967fa.accept_16_15_7_3_1_4273 63 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 259 (accept_3_3 62 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 259 (Polychromatic418967fa.accept_15_1_12_4_1_2022 61 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 259 (accept_3_3 59 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 259 (accept_3_3 56 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 259 (Polychromatic418967fa.accept_15_9_12_4_1_2023 54 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 259 (accept_3_3 53 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 259
  (Polychromatic418967fa.accept_19_13_11_12_1_3447 51 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 87 259 (accept_3_3 50 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 87 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 87 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 259 (accept_3_3 47 87 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 259 (accept_3_3 44 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 259 (Polychromatic418967fa.accept_16_11_7_3_1_3163 43 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 259 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 259 (accept_3_3 41 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 259 (accept_3_3 38 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 259 (accept_3_3 35 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 259 (accept_3_3 32 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 259 (accept_3_3 29 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 259
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 259 (accept_3_3 26 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 259 (Polychromatic418967fa.accept_14_11_3_7_1_604 25 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 259 (Polychromatic418967fa.accept_14_10_3_7_1_1975 24 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 259 (accept_3_3 23 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 87 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 259 (accept_3_3 20 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 259 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 259 (accept_3_3 17 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 259
  (Polychromatic418967fa.accept_16_15_7_3_1_4273 15 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 259 (accept_3_3 14 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 259 (accept_3_3 11 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 259 (accept_3_3 8 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  259 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 87 259 (Polychromatic418967fa.accept_17_6_2_4_1_2421 6 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 259 (accept_3_3 5 87 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 259 (accept_3_3 2 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87
  259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 87 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 87 259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86
  259 (allA_of_3_1 86 86 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 259 (allA_succ_of_accept 84 85 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 259 (accept_3_3 83 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 259 (accept_3_3 80 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 259 (Polychromatic418967fa.accept_19_3_9_12_1_6253 79 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 259 (accept_3_3 77 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 76 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 259 (accept_3_3 74 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 259
  (Polychromatic418967fa.accept_16_8_5_3_1_4297 72 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 259 (accept_3_3 71 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 259 (accept_3_3 68 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 67 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 259 (accept_3_3 65 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 259 (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 259 (accept_3_3 62 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 85 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 259 (accept_3_3 59 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 259 (accept_3_3 56 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 259 (accept_3_3 53 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 52 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 259 (accept_3_3 50 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 259 (Polychromatic418967fa.accept_13_10_7_12_1_2782 49 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 259 (accept_3_3 47 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 259 (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 259 (accept_3_3 44 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 259 (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 85
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 259 (accept_3_3 41 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 259 (Polychromatic418967fa.accept_16_8_5_3_1_4297 40 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 259 (accept_3_3 38 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 259
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 259 (accept_3_3 35 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 259 (accept_3_3 32 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 259 (accept_3_3 29 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 259 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 259 (accept_3_3 26 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 259 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 85 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 259 (accept_3_3 23 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 259 (accept_3_3 20 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 259 (accept_3_3 17 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 259 (accept_3_3 14 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 259 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 259 (accept_3_3 11 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 259 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 259 (accept_3_3 8 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 259 (accept_3_3 5 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 85 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 259 (accept_3_3 2 85 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 259
  (allA_succ_of_accept 83 84 259 (accept_3_3 83 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 259 (Polychromatic418967fa.accept_15_6_9_4_1_1227 81 84 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 259 (accept_3_3 80 84 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 84 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 84 259 7 11 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 76 84 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 84 259 (Polychromatic418967fa.accept_10_5_4_9_1_420 75 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 259 (accept_3_3 74 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 73
  84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 259
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 72 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 259 (accept_3_3 71 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84
  259 7 10 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  84 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 259 (accept_3_3 68 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 84 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 259 (Polychromatic418967fa.accept_15_6_9_4_1_1227 66 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 259 (accept_3_3 65 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 64
  84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84 259 7 9 12 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 84 259 (accept_3_3 62
  84 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 259
  (Polychromatic418967fa.accept_19_4_8_12_1_4757 61 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 84 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 259 (accept_3_3 59 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 84 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 84 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 84 259 (Polychromatic418967fa.accept_13_5_6_12_1_2750
  57 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 259 7 8 12 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 259
  (Polychromatic418967fa.accept_8_7_4_3_1_156 55 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 84 259 (Polychromatic418967fa.accept_13_2_6_12_1_1334 54 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 259 (accept_3_3 53 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 84 259 (Polychromatic418967fa.accept_24_4_12_19_1_12489 52 84 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 84 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 84 259 (accept_3_3 50 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 84
  259 7 7 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  84 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 84 259 (accept_3_3 47 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 84 259 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 259 (accept_3_3 44 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 259 (Polychromatic418967fa.accept_10_3_4_9_1_15 43
  84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 259 7 6 12 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 259 (accept_3_3 41
  84 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 40 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 84 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 259 (accept_3_3 38 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 84 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 84 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 259
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 84 259 7 5 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 84 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 34 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 259 (accept_3_3 32 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 31
  84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 259
  (Polychromatic418967fa.accept_19_11_8_12_1_6204 30 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 259 (accept_3_3 29 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84
  259 7 4 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  84 259 (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 259 (accept_3_3 26 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 259 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 259 (accept_3_3 23 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 22
  84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 259 7 3 12 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 259 (accept_3_3 20
  84 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 259
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 84 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 259 (accept_3_3 17 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 84 259 (Polychromatic418967fa.accept_22_16_18_17_1_15767 16 84 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 259
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 84 259 7 2 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 84 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 259 (accept_3_3 11 84 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 10
  84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 259
  (Polychromatic418967fa.accept_20_9_4_19_1_10052 9 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 84 259 (accept_3_3 8 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 84 259
  7 1 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 84
  259 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 259 (accept_3_3 5 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  259 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 84 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 259 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 259 (accept_3_3 2 84 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 259 (allA_of_3_1
  83 83 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 259 (allA_succ_of_accept 81 82 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 259 (accept_3_3 80 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 259 (Polychromatic418967fa.accept_14_9_12_7_1_597 79 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 259 (accept_3_3 77 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 259 (accept_3_3 74 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 72 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 259 (accept_3_3 71 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 259 (Polychromatic418967fa.accept_13_5_4_12_1_2058 70 82
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 259 (accept_3_3 68 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 259 (accept_3_3 65 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 259 (accept_3_3 62 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 259 (accept_3_3 59 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 259 (accept_3_3 56 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 259 (Polychromatic418967fa.accept_13_3_4_12_1_36 55 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 259 (Polychromatic418967fa.accept_11_10_5_6_1_1842 54 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 259 (accept_3_3 53 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 82 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 259 (accept_3_3 50 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 259 (accept_3_3 47 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 46 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 259 (accept_3_3 44 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 259 (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 259 (accept_3_3 41 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 259 (accept_3_3 38 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 259 (Polychromatic418967fa.accept_19_17_6_12_1_7757 36 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 259 (accept_3_3 35 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 82 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 259 (accept_3_3 32 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 259 (accept_3_3 29 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 259 (accept_3_3 26 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 259 (accept_3_3 23 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 259 (accept_3_3 20 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 259 (Polychromatic418967fa.accept_14_5_12_7_1_2767 19 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 259 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 259 (accept_3_3 17 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 82 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 259 (accept_3_3 14 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 259 (accept_3_3 11 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 259 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 82 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 259 (accept_3_3 8 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  259 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 82 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 82 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 259 (accept_3_3 5 82 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 82 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 259 (accept_3_3 2 82 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 259
  (allA_succ_of_accept 80 81 259 (accept_3_3 80 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 259 (Polychromatic418967fa.accept_11_2_4_6_1_2412 79 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 259 (accept_3_3 77 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 259
  (Polychromatic418967fa.accept_10_5_1_9_1_791 75 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 259 (accept_3_3 74 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 259 (Polychromatic418967fa.accept_14_3_11_7_1_1260 73 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 259 (accept_3_3 71 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 259
  (Polychromatic418967fa.accept_13_4_3_12_1_2066 69 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 259 (accept_3_3 68 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 259 (Polychromatic418967fa.accept_13_2_3_12_1_735 67 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 259 (accept_3_3 65 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 259 (accept_3_3 62 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 259 (Polychromatic418967fa.accept_13_9_3_12_1_2025 61 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 259 (Polychromatic418967fa.accept_14_4_11_7_1_1234 60 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 259 (accept_3_3 59 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 259
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 259 (accept_3_3 56 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 55 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 259 (accept_3_3 53 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 259 (accept_3_3 50 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 259 (Polychromatic418967fa.accept_19_11_5_12_1_3439 49 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 259 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 259 (accept_3_3 47 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 259
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 259 (accept_3_3 44 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 259 (Polychromatic418967fa.accept_13_4_3_12_1_2066 43 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 259 (accept_3_3 41 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 259 (accept_3_3 38 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 259 (Polychromatic418967fa.accept_17_3_13_4_1_8530 37 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 259 (Polychromatic418967fa.accept_16_4_1_3_1_6581 36 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 259 (accept_3_3 35 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 259
  (Polychromatic418967fa.accept_21_12_18_7_1_6740 33 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 259 (accept_3_3 32 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 259 (Polychromatic418967fa.accept_14_3_11_7_1_1260 31 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 259 (accept_3_3 29 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 259 (accept_3_3 26 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 259 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 259 (accept_3_3 23 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 259
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 21 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 259 (accept_3_3 20 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 259 (Polychromatic418967fa.accept_21_19_18_7_1_8388 19 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 259 (accept_3_3 17 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 259
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 259 (accept_3_3 14 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 259 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 259 (accept_3_3 11 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 259
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 259 (accept_3_3 8 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  259 (Polychromatic418967fa.accept_19_7_5_12_1_7756 7 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 259 (accept_3_3 5 81 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 259 (accept_3_3 2 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  259 (Polychromatic418967fa.accept_19_1_5_12_1_6249 1 81 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 259 (allA_of_3_1 80 80 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 259
  (allA_succ_of_accept 78 79 259 (Polychromatic418967fa.accept_17_10_11_4_1_2522 78 79 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 259 (accept_3_3 77 79 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 76 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 259 (Polychromatic418967fa.accept_14_5_9_7_1_590
  75 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 259 (accept_3_3 74
  79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 259
  (Polychromatic418967fa.accept_13_8_1_12_1_762 73 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 259 (Polychromatic418967fa.accept_14_2_9_7_1_5633 72 79 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 259 (accept_3_3 71 79 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 259 (Polychromatic418967fa.accept_11_4_2_6_1_389 70 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 259 (Polychromatic418967fa.accept_21_6_16_7_1_3714
  69 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 259 (accept_3_3 68
  79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 259
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 67 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 79 259 (Polychromatic418967fa.accept_16_2_15_3_1_1300 66 79 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 259 (accept_3_3 65 79 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 259 (Polychromatic418967fa.accept_19_7_3_12_1_4787 64 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 259
  (Polychromatic418967fa.accept_13_11_1_12_1_742 63 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 259 (accept_3_3 62 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 259 (Polychromatic418967fa.accept_14_5_9_7_1_590 61 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 259 (accept_3_3 59 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 259 (Polychromatic418967fa.accept_14_2_9_7_1_5633 58 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 259
  (Polychromatic418967fa.accept_13_5_1_12_1_740 57 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 259 (accept_3_3 56 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 259 (Polychromatic418967fa.accept_16_7_15_3_1_1302 55 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 259 (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 259 (accept_3_3 53 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 79 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 259
  (Polychromatic418967fa.accept_19_13_3_12_1_6186 51 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 259 (accept_3_3 50 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 259 (Polychromatic418967fa.accept_17_15_11_4_1_7218 49 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 259 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 259 (accept_3_3 47 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 259 (Polychromatic418967fa.accept_21_4_16_7_1_11401 46 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 259
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 45 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 259 (accept_3_3 44 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 259 (Polychromatic418967fa.accept_16_11_15_3_1_1304 43 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 259 (Polychromatic418967fa.accept_23_19_10_6_1_12573 42 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 259 (accept_3_3 41 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 259 (Polychromatic418967fa.accept_14_12_9_7_1_2762 40 79
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 259
  (Polychromatic418967fa.accept_16_7_15_3_1_1302 39 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 259 (accept_3_3 38 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 259 (Polychromatic418967fa.accept_11_4_2_6_1_389 37 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 259 (accept_3_3 35 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 259 (Polychromatic418967fa.accept_13_8_1_12_1_762 34 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 259
  (Polychromatic418967fa.accept_14_5_9_7_1_590 33 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 259 (accept_3_3 32 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 259 (Polychromatic418967fa.accept_13_5_1_12_1_740 31 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 259 (Polychromatic418967fa.accept_14_2_9_7_1_5633 30 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 259 (accept_3_3 29 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 259
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 259 (accept_3_3 26 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 259 (Polychromatic418967fa.accept_21_4_16_7_1_11401 25 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 259 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 259 (accept_3_3 23 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 259 (Polychromatic418967fa.accept_21_1_16_7_1_3763 22 79
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 259
  (Polychromatic418967fa.accept_13_8_1_12_1_762 21 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 259 (accept_3_3 20 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 259 (Polychromatic418967fa.accept_14_5_9_7_1_590 19 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 259 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 259 (accept_3_3 17 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 259 (Polychromatic418967fa.accept_14_2_9_7_1_5633 16 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 259
  (Polychromatic418967fa.accept_11_4_2_6_1_389 15 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 259 (accept_3_3 14 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 259 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 259 (accept_3_3 11 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 259 (Polychromatic418967fa.accept_17_10_11_4_1_2522 10 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 259
  (Polychromatic418967fa.accept_19_9_3_12_1_6191 9 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 259 (accept_3_3 8 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  259 (Polychromatic418967fa.accept_16_7_15_3_1_1302 7 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 259 (Polychromatic418967fa.accept_17_6_11_4_1_1525 6 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 259 (accept_3_3 5 79 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 79 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 259
  (Polychromatic418967fa.accept_21_3_16_7_1_12858 3 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 259 (accept_3_3 2 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  259 (Polychromatic418967fa.accept_21_1_16_7_1_3763 1 79 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 79 259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  78 259 (allA_succ_of_accept 77 78 259 (accept_3_3 77 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 78 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 78 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 78 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 259 (accept_3_3 74 78 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 259
  (Polychromatic418967fa.accept_21_9_15_7_1_5156 72 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 259 (accept_3_3 71 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 259 (Polychromatic418967fa.accept_28_14_22_7_1_11829 70 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 259 (accept_3_3 68 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 78 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 259 (accept_3_3 65 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 259 (Polychromatic418967fa.accept_18_9_6_7_1_6719 63 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 259 (accept_3_3 62 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 259
  (Polychromatic418967fa.accept_11_5_1_6_1_774 60 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 259 (accept_3_3 59 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 259 (accept_3_3 56 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 78 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 259
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 259 (accept_3_3 53 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 259 (Polychromatic418967fa.accept_15_7_3_4_1_574 52 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 259 (accept_3_3 50 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 259 (accept_3_3 47 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 259 (accept_3_3 44 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 259 (Polychromatic418967fa.accept_14_1_8_7_1_1253 43 78 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 259
  (Polychromatic418967fa.accept_19_4_2_12_1_10527 42 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 259 (accept_3_3 41 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 259 (accept_3_3 38 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 259
  (Polychromatic418967fa.accept_19_17_2_12_1_4751 36 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 259 (accept_3_3 35 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 259 (accept_3_3 32 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 78 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 259 (accept_3_3 29 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 259 (accept_3_3 26 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 259
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 259 (accept_3_3 23 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 259 (accept_3_3 20 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 78 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 259
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 259 (accept_3_3 17 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 259 (Polychromatic418967fa.accept_14_1_8_7_1_1253 15 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 259 (accept_3_3 14 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 259 (accept_3_3 11 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 259 (accept_3_3 8 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 78 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 259
  (Polychromatic418967fa.accept_14_6_8_7_1_589 6 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 259 (accept_3_3 5 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  259 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 78 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 78 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 259 (accept_3_3 2 78 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 259 (allA_of_3_1 77 77
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 259 (allA_succ_of_accept 75 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 259 (accept_3_3 74 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 259 (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 259 (accept_3_3 71 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 76 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 259 (accept_3_3 68 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 259 (Polychromatic418967fa.accept_18_13_4_7_1_4086 67 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 259 (accept_3_3 65 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 259 (accept_3_3 62 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 259 (Polychromatic418967fa.accept_21_19_13_7_1_3706 61 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 259 (accept_3_3 59 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 259 (accept_3_3 56 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 259 (Polychromatic418967fa.accept_23_8_7_6_1_15766 54 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 259 (accept_3_3 53 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 259 (Polychromatic418967fa.accept_16_4_12_3_1_2180 52 76
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 259 (accept_3_3 50 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 259 (Polychromatic418967fa.accept_11_5_10_6_1_793 49 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 259 (accept_3_3 47 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 259 (accept_3_3 44 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 259 (accept_3_3 41 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 259 (Polychromatic418967fa.accept_13_1_11_12_1_1322 40 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 259 (accept_3_3 38 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 259 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 259 (accept_3_3 35 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 76 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 259 (accept_3_3 32 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 259 (accept_3_3 29 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 259 (accept_3_3 26 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 259 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 259 (accept_3_3 23 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 259 (accept_3_3 20 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 259 (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 259 (accept_3_3 17 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 259 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 259 (accept_3_3 14 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 259 (accept_3_3 11 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 76 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 259 (accept_3_3 8 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  259 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 76 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 76 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 259 (accept_3_3 5 76 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 259 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 76 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 259 (accept_3_3 2 76 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 259 (allA_succ_of_accept
  74 75 259 (accept_3_3 74 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 259
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 259 (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 75 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 259 (accept_3_3 71 75 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 69
  75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 259 (accept_3_3 68 75
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 75 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 66 75 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 259 (accept_3_3 65 75 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 259
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 75 259 (accept_3_3 62 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 75 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 75 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 259 (accept_3_3 59 75 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 58
  75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 259 (accept_3_3 56 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  75 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 75 259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 259 (accept_3_3 53 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 75 259 (accept_3_3 50 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  75 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 75 259 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 259 (accept_3_3 47 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 75 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 259 (accept_3_3 44 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 259 (Polychromatic418967fa.accept_21_1_12_7_1_3783 43 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 259 (accept_3_3 41 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 259
  (Polychromatic418967fa.accept_16_7_11_3_1_1330 39 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 259 (accept_3_3 38 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 259 (accept_3_3 35 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 259 (accept_3_3 32 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 259 (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 259 (accept_3_3 29 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 259
  (Polychromatic418967fa.accept_18_9_3_7_1_9449 27 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 259 (accept_3_3 26 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 259 (accept_3_3 23 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 259
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 259 (accept_3_3 20 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 259 (Polychromatic418967fa.accept_21_18_12_7_1_6712 18 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 259 (accept_3_3 17 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 259 (accept_3_3 14 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 259 (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 259 (accept_3_3 11 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 75 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 259 (accept_3_3 8 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  259 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 259 (accept_3_3 5 75 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 259
  (Polychromatic418967fa.accept_11_3_9_6_1_105 3 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 259 (accept_3_3 2 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75
  259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 75 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 259
  (allA_of_3_1 74 74 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 259 (allA_succ_of_accept 72 73 259
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 259 (accept_3_3 71 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 259 (accept_3_3 68 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 259 (accept_3_3 65 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 64 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 259 (Polychromatic418967fa.accept_19_6_16_12_1_6118 63 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 259 (accept_3_3 62 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 259 (Polychromatic418967fa.accept_13_9_8_12_1_2031 61 73
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 259 (accept_3_3 59 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 259 (accept_3_3 56 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 55 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 259 (accept_3_3 53 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 259 (Polychromatic418967fa.accept_14_10_3_7_1_1975 52 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 259 (accept_3_3 50 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 259 (accept_3_3 47 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 259 (accept_3_3 44 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 259 (Polychromatic418967fa.accept_13_4_8_12_1_3526 43 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 259 (accept_3_3 41 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 259 (accept_3_3 38 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 259 (Polychromatic418967fa.accept_21_16_10_7_1_3782 37 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 259
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 259 (accept_3_3 35 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 259 (accept_3_3 32 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 259 (accept_3_3 29 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 259 (Polychromatic418967fa.accept_16_12_9_3_1_5363 28 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 259 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 259 (accept_3_3 26 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 259 (Polychromatic418967fa.accept_14_11_3_7_1_604 25 73 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 259 (accept_3_3 23 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 259 (accept_3_3 20 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 259 (Polychromatic418967fa.accept_21_19_10_7_1_8384 19 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 259 (accept_3_3 17 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 259 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 259 (accept_3_3 14 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 259 (accept_3_3 11 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 259 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 259 (accept_3_3 8 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 259 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 73 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 259 (accept_3_3 5 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 73 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 73 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 259 (accept_3_3 2 73 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 73 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 259 (allA_succ_of_accept 71
  72 259 (accept_3_3 71 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 259
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 70 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 259 (Polychromatic418967fa.accept_13_4_7_12_1_2823 69 72 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 259 (accept_3_3 68 72 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 67 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 259 (Polychromatic418967fa.accept_21_3_9_7_1_8369
  66 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 259 (accept_3_3 65
  72 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 259
  (Polychromatic418967fa.accept_19_7_15_12_1_4800 64 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 72 259 (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 72 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 259 (accept_3_3 62 72 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 72 259 (Polychromatic418967fa.accept_10_1_2_9_1_152 61 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 259 (Polychromatic418967fa.accept_13_8_7_12_1_3637
  60 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 259 (accept_3_3 59
  72 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 72 259
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 58 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 72 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 57 72 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 259 (accept_3_3 56 72 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 72 259 (Polychromatic418967fa.accept_19_17_15_12_1_10534 55 72 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 259
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 54 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 72 259 (accept_3_3 53 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  72 259 (Polychromatic418967fa.accept_15_7_12_4_1_1236 52 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 259 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 259 (accept_3_3 50 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 259 (Polychromatic418967fa.accept_13_10_7_12_1_2782 49 72 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 259
  (Polychromatic418967fa.accept_21_6_9_7_1_3752 48 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 259 (accept_3_3 47 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 259 (Polychromatic418967fa.accept_15_1_12_4_1_2022 46 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 259 (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 72 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 259 (accept_3_3 44 72 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 259 (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 72
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 259
  (Polychromatic418967fa.accept_20_2_12_19_1_11651 42 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 72 259 (accept_3_3 41 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 259 (Polychromatic418967fa.accept_14_12_2_7_1_1243 40 72 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 72 259 (Polychromatic418967fa.accept_15_9_12_4_1_2023 39 72
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 259 (accept_3_3 38 72 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 259 (Polychromatic418967fa.accept_10_7_2_9_1_775
  37 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 259
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 259 (accept_3_3 35 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 259 (Polychromatic418967fa.accept_13_8_7_12_1_3637 34 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 259 (Polychromatic418967fa.accept_14_5_2_7_1_2804 33 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 259 (accept_3_3 32 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 259 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 72 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 259
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 259 (accept_3_3 29 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 259 (Polychromatic418967fa.accept_16_12_8_3_1_4241 28 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 259 (accept_3_3 26 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 259 (Polychromatic418967fa.accept_19_6_15_12_1_6263 25 72 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 259
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 259 (accept_3_3 23 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 259 (Polychromatic418967fa.accept_15_7_12_4_1_1236 22 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 259 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 259 (accept_3_3 20 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 259 (Polychromatic418967fa.accept_13_6_7_12_1_3504 19 72 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 259
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 259 (accept_3_3 17 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 259 (Polychromatic418967fa.accept_15_1_12_4_1_2022 16 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 259 (Polychromatic418967fa.accept_21_15_9_7_1_3780 15 72 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 259 (accept_3_3 14 72 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 259 (Polychromatic418967fa.accept_16_13_8_3_1_5374 13 72
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 259
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 259 (accept_3_3 11 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 259 (Polychromatic418967fa.accept_13_10_7_12_1_2782 10 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 259 (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 259 (accept_3_3 8 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 72 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 259
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 259 (accept_3_3 5 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  259 (Polychromatic418967fa.accept_13_4_7_12_1_2823 4 72 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 259 (Polychromatic418967fa.accept_19_3_15_12_1_9110 3 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 259 (accept_3_3 2 72 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 259 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 72 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 259 (allA_of_3_1 71 71 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 259 (allA_succ_of_accept 69 70 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 259 (accept_3_3 68 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 259 (Polychromatic418967fa.accept_13_2_5_12_1_2043 67 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 259 (Polychromatic418967fa.accept_13_1_5_12_1_306 66 70 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 259 (accept_3_3 65 70 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 70 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 70 259 7 9 10 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 70 259 (accept_3_3 62 70 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 70 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 70 259
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 60 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 70 259 (accept_3_3 59 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  70 259 (Polychromatic418967fa.accept_13_6_5_12_1_307 58 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 70 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 259 7 8 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 70 259 (Polychromatic418967fa.accept_18_1_16_7_1_2897
  55 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 70 259
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 54 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 70 259 (accept_3_3 53 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  70 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 70 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 70 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 70 259 (accept_3_3 50 70 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 49 70 259 7 7 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 48 70 259 (Polychromatic418967fa.accept_23_2_1_6_1_14136 48 70 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 259 (accept_3_3 47 70 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 259 (Polychromatic418967fa.accept_11_2_4_6_1_2412 46 70 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 259 (accept_3_3 44 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 259 (Polychromatic418967fa.accept_13_4_5_12_1_751 43 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 70 259 7 6 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 70 259 (accept_3_3 41 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 70 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 70 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 70 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 259 (accept_3_3 38 70 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 259
  (Polychromatic418967fa.accept_15_6_10_4_1_150 36 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 70 259 7 5 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 70 259 (Polychromatic418967fa.accept_13_8_5_12_1_2755 34 70 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 259 (accept_3_3 32 70 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 259
  (Polychromatic418967fa.accept_20_11_10_19_1_8714 31 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 259 (Polychromatic418967fa.accept_13_4_5_12_1_751 30 70 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 259 (accept_3_3 29 70 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 259 7 4 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 70 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 259 (accept_3_3 26 70 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 259
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 259 (accept_3_3 23 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 70 259 7 3 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 70 259 (accept_3_3 20 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 70 259 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 70 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 259 (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 70 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 259 (accept_3_3 17 70 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 259 (Polychromatic418967fa.accept_12_4_10_7_1_149
  16 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 70 259 7 2 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 70 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 259 (Polychromatic418967fa.accept_17_12_2_4_1_11050 12 70
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 259 (accept_3_3 11 70 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 259
  (Polychromatic418967fa.accept_22_10_4_17_1_7993 10 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 70 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 259 (accept_3_3 8 70 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 7 70 259 7 1 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 70 259 (Polychromatic418967fa.accept_13_6_5_12_1_307 6 70 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 259 (accept_3_3 5 70 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 70 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 259 (accept_3_3 2 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 259
  (allA_succ_of_accept 68 69 259 (accept_3_3 68 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 259 (accept_3_3 65 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 259
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 259 (accept_3_3 62 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 259 (Polychromatic418967fa.accept_25_11_19_9_1_15765 61 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 259 (Polychromatic418967fa.accept_13_8_4_12_1_2753 60 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 259 (accept_3_3 59 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 259 (accept_3_3 56 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 259 (accept_3_3 53 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 259 (accept_3_3 50 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 259 (accept_3_3 47 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 259
  (Polychromatic418967fa.accept_21_3_6_7_1_6750 45 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 259 (accept_3_3 44 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 259 (Polychromatic418967fa.accept_14_1_13_7_1_1205 43 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 259 (accept_3_3 41 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 259 (accept_3_3 38 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 259 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 259 (accept_3_3 35 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 259
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 259 (accept_3_3 32 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 259 (accept_3_3 29 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 259 (accept_3_3 26 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 259 (Polychromatic418967fa.accept_15_10_9_4_1_2924 25 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 259 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 259 (accept_3_3 23 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 259 (accept_3_3 20 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 259 (accept_3_3 17 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 259 (accept_3_3 14 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 259 (accept_3_3 11 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 259
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 259 (accept_3_3 8 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 69 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 259 (accept_3_3 5 69 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 259 (accept_3_3 2 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69
  259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 69 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 259 (allA_of_3_1
  68 68 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 259 (allA_succ_of_accept 66 67 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 259 (accept_3_3 65 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 259 (Polychromatic418967fa.accept_15_3_7_4_1_1225 63 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 259 (accept_3_3 62 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 259 (Polychromatic418967fa.accept_21_19_4_7_1_3775 61 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 259 (accept_3_3 59 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 259 (Polychromatic418967fa.accept_10_8_7_9_1_425 58 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 259 (accept_3_3 56 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 259
  (Polychromatic418967fa.accept_17_3_16_4_1_2416 54 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 259 (accept_3_3 53 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 259 (Polychromatic418967fa.accept_10_2_7_9_1_783 52 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 259 (accept_3_3 50 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 49 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 259 (accept_3_3 47 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 259 (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 259 (accept_3_3 44 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 259 (Polychromatic418967fa.accept_13_4_2_12_1_2800 43 67
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 259 (accept_3_3 41 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 259 (Polychromatic418967fa.accept_11_7_1_6_1_1281 40 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 259 (accept_3_3 38 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 259
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 259 (accept_3_3 35 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 259 (Polychromatic418967fa.accept_21_13_4_7_1_5190 34 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 259 (accept_3_3 32 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 259 (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 259 (accept_3_3 29 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 259 (accept_3_3 26 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 259 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 259 (accept_3_3 23 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 259 (Polychromatic418967fa.accept_10_2_7_9_1_783 22 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 259 (accept_3_3 20 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 259
  (Polychromatic418967fa.accept_10_8_7_9_1_425 18 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 259 (accept_3_3 17 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 259 (accept_3_3 14 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 259 (Polychromatic418967fa.accept_21_13_4_7_1_5190 13 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 259 (accept_3_3 11 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 259 (Polychromatic418967fa.accept_19_9_10_12_1_6161 9 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 259 (accept_3_3 8 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 259 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 259 (accept_3_3 5 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  259 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 67 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 259 (accept_3_3 2 67 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 67 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 259 (allA_succ_of_accept 65 66
  259 (accept_3_3 65 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 259
  (Polychromatic418967fa.accept_9_1_3_7_1_6 64 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 66 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 259 (accept_3_3 62 66 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 60
  66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 259 (accept_3_3 59 66
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 58 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 66 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 259 (accept_3_3 56 66 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 66 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 259 (Polychromatic418967fa.accept_13_2_1_12_1_1326
  54 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 259 (accept_3_3 53
  66 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 259
  (Polychromatic418967fa.accept_19_14_9_12_1_9113 52 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 66 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 66 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 259 (accept_3_3 50 66 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 66 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 259
  (Polychromatic418967fa.accept_19_10_9_12_1_4774 48 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 66 259 (accept_3_3 47 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  66 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 66 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 259 (accept_3_3 44 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 66 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 66 259 (accept_3_3 41 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  66 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 66 259 (Polychromatic418967fa.accept_14_11_10_7_1_1948 39 66 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 259 (accept_3_3 38 66 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 259
  (Polychromatic418967fa.accept_17_2_15_4_1_4723 36 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 259 (accept_3_3 35 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  66 259 (Polychromatic418967fa.accept_13_8_1_12_1_762 34 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 259 (accept_3_3 32 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 259
  (Polychromatic418967fa.accept_20_10_6_19_1_5691 30 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 66 259 (accept_3_3 29 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  66 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 66 259 (Polychromatic418967fa.accept_17_10_15_4_1_5967 27 66 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 259 (accept_3_3 26 66 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 259 (accept_3_3 23 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  66 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 66 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 259 (accept_3_3 20 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 66 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 259
  (Polychromatic418967fa.accept_13_5_1_12_1_740 18 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 259 (accept_3_3 17 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  66 259 (Polychromatic418967fa.accept_17_16_15_4_1_8559 16 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 259 (accept_3_3 14 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 259
  (Polychromatic418967fa.accept_21_12_3_7_1_14223 12 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 66 259 (accept_3_3 11 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  66 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 66 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 259 (accept_3_3 8 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 259 (Polychromatic418967fa.accept_20_7_6_19_1_2949 7 66 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 259 (accept_3_3 5 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  259 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 66 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 66 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 66 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 259 (accept_3_3 2 66 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 66 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 259 (allA_of_3_1 65 65 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 259 (allA_succ_of_accept 63 64 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 259 (accept_3_3 62 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 259 (Polychromatic418967fa.accept_19_4_7_12_1_6201 61 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 259 (accept_3_3 59 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 64 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 259 (accept_3_3 56 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 259 (Polychromatic418967fa.accept_10_5_4_9_1_420 55 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 259 (Polychromatic418967fa.accept_17_3_13_4_1_8530 54 64 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 259 (accept_3_3 53 64 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 259 (Polychromatic418967fa.accept_19_14_7_12_1_7732 52 64
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 259 (accept_3_3 50 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 259 (accept_3_3 47 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 64 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 259 (accept_3_3 44 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 259 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 259 (accept_3_3 41 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 64 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 259 (accept_3_3 38 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 259 (Polychromatic418967fa.accept_17_3_13_4_1_8530 37 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 259 (accept_3_3 35 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 64 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 259 (accept_3_3 32 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 259 (accept_3_3 29 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 64 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 259 (accept_3_3 26 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 259 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 259 (accept_3_3 23 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 64 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 259 (accept_3_3 20 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 259 (Polychromatic418967fa.accept_21_19_1_7_1_3724 19 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 259 (accept_3_3 17 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 259 (Polychromatic418967fa.accept_19_16_7_12_1_6252 16 64 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 259 (accept_3_3 14 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 259 (accept_3_3 11 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 64 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 259 (accept_3_3 8 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  259 (Polychromatic418967fa.accept_25_7_14_9_1_14048 7 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 64 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 259 (accept_3_3 5 64 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 64 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 259 (accept_3_3 2 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  259 (Polychromatic418967fa.accept_14_1_8_7_1_1253 1 64 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 64 259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 259
  (allA_succ_of_accept 62 63 259 (accept_3_3 62 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 259 (Polychromatic418967fa.accept_15_1_3_4_1_1217 61 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 63 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 259 (accept_3_3 59 63 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 63 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 63 259 7 8 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 63 259 (Polychromatic418967fa.accept_16_7_15_3_1_1302 55 63 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 63 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 259 (accept_3_3 53 63 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52
  63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 259
  (Polychromatic418967fa.accept_19_13_6_12_1_6109 51 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 259 (accept_3_3 50 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63
  259 7 7 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  63 259 (Polychromatic418967fa.accept_19_10_6_12_1_10562 48 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 259 (accept_3_3 47 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 63 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 259 (Polychromatic418967fa.accept_12_9_3_7_1_924 45 63 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 259 (accept_3_3 44 63 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 259
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 43 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 63 259 7 6 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 63 259 (accept_3_3 41 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  63 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 63 259 (Polychromatic418967fa.accept_16_7_15_3_1_1302 39 63 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 259 (accept_3_3 38 63 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 259 (Polychromatic418967fa.accept_15_7_3_4_1_574 37 63 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 259
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 63 259 7 5 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 63 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 259 (Polychromatic418967fa.accept_12_9_3_7_1_924 33 63 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 259 (accept_3_3 32 63 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 259 (Polychromatic418967fa.accept_15_1_3_4_1_1217
  31 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 259
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 259 (accept_3_3 29 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63
  259 7 4 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  63 259 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 63 259 (accept_3_3 26 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 259 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 63 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 63 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 259 (accept_3_3 23 63 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 259 7 3 9 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 259 (accept_3_3 20
  63 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 259
  (Polychromatic418967fa.accept_17_2_12_4_1_5987 19 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 63 259 (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 63 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 259 (accept_3_3 17 63 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 63 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 259
  (Polychromatic418967fa.accept_19_15_6_12_1_7746 15 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 63 259 7 2 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 63 259 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 63 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 259 (accept_3_3 11 63 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10
  63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 259 (accept_3_3 8 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 259
  7 1 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 63 259
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 259 (accept_3_3 5 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 63 259 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 63 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 259 (accept_3_3 2 63 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 63 259 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 63 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 259 (allA_of_3_1 62 62 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 259 (allA_succ_of_accept 60 61 259
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 60 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 259 (accept_3_3 59 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 259 (Polychromatic418967fa.accept_15_12_1_4_1_2899 57 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 259 (accept_3_3 56 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 55 61 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 259 (accept_3_3 53 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 52 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 259 (Polychromatic418967fa.accept_14_9_5_7_1_1251 51 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 259 (accept_3_3 50 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 259 (Polychromatic418967fa.accept_13_10_9_12_1_2814 49 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 259
  (Polychromatic418967fa.accept_10_8_1_9_1_413 48 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 259 (accept_3_3 47 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 259 (accept_3_3 44 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 259 (Polychromatic418967fa.accept_19_5_4_12_1_7773 43 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 259 (accept_3_3 41 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 259 (Polychromatic418967fa.accept_14_12_5_7_1_2010 40 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 259 (Polychromatic418967fa.accept_19_1_4_12_1_6275 39 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 259 (accept_3_3 38 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 259 (Polychromatic418967fa.accept_14_9_5_7_1_1251 37 61 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 259
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 259 (accept_3_3 35 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 259 (Polychromatic418967fa.accept_15_3_1_4_1_1246 33 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 259 (accept_3_3 32 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 259 (Polychromatic418967fa.accept_16_15_13_3_1_4215 31 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 259 (accept_3_3 29 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 259 (Polychromatic418967fa.accept_10_8_1_9_1_413 28 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 259 (Polychromatic418967fa.accept_15_12_1_4_1_2899 27 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 259 (accept_3_3 26 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 61 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 259
  (Polychromatic418967fa.accept_16_8_13_3_1_4253 24 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 259 (accept_3_3 23 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 259 (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 259 (accept_3_3 20 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 259 (Polychromatic418967fa.accept_25_19_11_9_1_15764 19 61
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 259 (accept_3_3 17 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 259 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 259 (accept_3_3 14 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 259 (Polychromatic418967fa.accept_21_13_19_7_1_5162 13 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 259
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 259 (accept_3_3 11 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 259 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 259 (accept_3_3 8 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 259 (Polychromatic418967fa.accept_19_7_4_12_1_4769 7 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 259 (accept_3_3 5 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  259 (Polychromatic418967fa.accept_21_4_19_7_1_5142 4 61 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 259 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 259 (accept_3_3 2 61 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 259 (Polychromatic418967fa.accept_16_1_13_3_1_2168 1 61 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 259 (allA_succ_of_accept 59 60 259
  (accept_3_3 59 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 259
  (Polychromatic418967fa.accept_9_4_6_7_1_286 58 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 60 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 60 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 259 (accept_3_3 56 60 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 60 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 60 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 259 (Polychromatic418967fa.accept_11_10_5_6_1_1842
  54 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 259 (accept_3_3 53
  60 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 259
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 52 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 60 259 (Polychromatic418967fa.accept_19_13_3_12_1_6186 51 60 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 259 (accept_3_3 50 60 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 60 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 48
  60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 259 (accept_3_3 47 60
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 259
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 60 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 60 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 259 (accept_3_3 44 60 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 60 259 (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 60 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 259
  (Polychromatic418967fa.accept_16_10_12_3_1_4252 42 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 259 (accept_3_3 41 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  60 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 259 (accept_3_3 38 60 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 60 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 259
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 259 (accept_3_3 35 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 259 (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 60 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 259 (accept_3_3 32 60 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 60 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 259 (accept_3_3 29 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 259 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 60 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 259 (accept_3_3 26 60 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 259 (Polychromatic418967fa.accept_14_11_4_7_1_609 25 60 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 259
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 259 (accept_3_3 23 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 259 (accept_3_3 20 60 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 60 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 259
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 259 (accept_3_3 17 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 259 (Polychromatic418967fa.accept_24_16_12_19_1_15763 16 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 60 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 259 (accept_3_3 14 60 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 60 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 259 (accept_3_3 11 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 259 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 60 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 259 (accept_3_3 8 60 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 259
  (Polychromatic418967fa.accept_21_6_18_7_1_3764 6 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 259 (accept_3_3 5 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  259 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 60 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 60 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 259 (accept_3_3 2 60 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 60 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 259 (allA_of_3_1 59 59 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 259
  (allA_succ_of_accept 57 58 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 259 (accept_3_3 56 58 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 58 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 259 (Polychromatic418967fa.accept_10_4_8_9_1_784
  54 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 259 (accept_3_3 53
  58 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 259
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 52 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 58 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 259 (accept_3_3 50 58 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 48
  58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 259 (accept_3_3 47 58
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 259 (Polychromatic418967fa.accept_9_1_4_7_1_7
  46 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 259 (accept_3_3 44 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 259 (Polychromatic418967fa.accept_19_5_1_12_1_6102 43 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 58 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 259 (accept_3_3 41 58 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 58 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 259 (accept_3_3 38 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 259 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 58 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 259 (accept_3_3 35 58 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 58 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 259 (accept_3_3 32 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 58 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 259 (accept_3_3 29 58 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 58 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 259 (accept_3_3 26 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 58 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 259 (accept_3_3 23 58 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 259 (Polychromatic418967fa.accept_21_1_16_7_1_3763 22 58 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 259 (accept_3_3 20 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 259 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 58 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 259 (accept_3_3 17 58 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 58 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 259 (accept_3_3 14 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 58 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 259 (accept_3_3 11 58 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 58 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 259 (accept_3_3 8 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  259 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 58 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 58 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 259 (accept_3_3 5 58 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 58 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 259 (accept_3_3 2 58 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 259 (allA_succ_of_accept 56 57 259
  (accept_3_3 56 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 259
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 259 (accept_3_3 53 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 51
  57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 259 (accept_3_3 50 57
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 259 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 259 (accept_3_3 47 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 259 (Polychromatic418967fa.accept_13_6_5_12_1_307
  45 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 259 (accept_3_3 44
  57 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 259
  (Polychromatic418967fa.accept_13_4_5_12_1_751 43 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 259 (accept_3_3 41 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 259 (Polychromatic418967fa.accept_12_3_9_7_1_472
  39 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 259 (accept_3_3 38
  57 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 259
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 259 (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 259 (accept_3_3 35 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 33
  57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 259 (accept_3_3 32 57
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 259 (accept_3_3 29 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 259 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 259 (accept_3_3 26
  57 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 259
  (Polychromatic418967fa.accept_24_1_9_19_1_12488 25 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 259 (accept_3_3 23 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 259 (Polychromatic418967fa.accept_13_8_5_12_1_2755
  21 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 259 (accept_3_3 20
  57 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 259
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 259 (accept_3_3 17 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 259 (accept_3_3 14 57
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 259 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 259 (accept_3_3 11 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 259 (Polychromatic418967fa.accept_15_9_12_4_1_2023
  9 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 259 (accept_3_3 8 57
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 259
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 57 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 259 (accept_3_3 5 57 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 57 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 3
  57 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 259 (accept_3_3 2 57 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 57
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 259 (allA_of_3_1 56 56 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 55 259 (allA_succ_of_accept 54 55 259
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 259 (accept_3_3 53 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 55 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 259 (accept_3_3 50 55 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 55 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 259 (accept_3_3 47 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 46 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 259 (Polychromatic418967fa.accept_20_5_15_19_1_4225 45 55 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 259 (accept_3_3 44 55 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 259 (Polychromatic418967fa.accept_13_4_3_12_1_2066 43 55
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 259 (accept_3_3 41 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 55 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 259 (accept_3_3 38 55 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 37 55 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 259
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 259 (accept_3_3 35 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 34 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 55 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 259 (accept_3_3 32 55 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 259 (accept_3_3 29 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 259 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 55 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 259 (accept_3_3 26 55 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 259 (Polychromatic418967fa.accept_16_9_7_3_1_614 25 55 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 259 (accept_3_3 23 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 55 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 259 (accept_3_3 20 55 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 259 (Polychromatic418967fa.accept_21_19_13_7_1_3706 19 55 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 259
  (Polychromatic418967fa.accept_19_18_17_12_1_4764 18 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 55 259 (accept_3_3 17 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 55 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 55 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 55 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 259 (accept_3_3 14 55 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 259
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 259 (accept_3_3 11 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 259 (Polychromatic418967fa.accept_16_10_7_3_1_6601 10 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 259 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 55 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 259 (accept_3_3 8 55 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 55 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 259 (accept_3_3 5 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  259 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 55 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 55 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 259 (accept_3_3 2 55 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 55 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 259)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 259 (allA_succ_of_accept 53 54 259 (accept_3_3 53 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 259 (Polychromatic418967fa.accept_16_4_6_3_1_1311 52 54 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 54 259 (Polychromatic418967fa.accept_14_9_12_7_1_597 51 54 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 259 (accept_3_3 50 54 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 259
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 259 (accept_3_3 47 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 259 (Polychromatic418967fa.accept_20_6_14_19_1_5669 46 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 259 (accept_3_3 44 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 259 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 54 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 259
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 42 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 259 (accept_3_3 41 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 259 (Polychromatic418967fa.accept_13_1_2_12_1_1299 40 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 259 (Polychromatic418967fa.accept_21_18_12_7_1_6712 39 54 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 259 (accept_3_3 38 54 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 259
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 259 (accept_3_3 35 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 259 (Polychromatic418967fa.accept_16_2_6_3_1_5396 34 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 259 (accept_3_3 32 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 259 (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 54 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 259
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 259 (accept_3_3 29 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 259 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 259 (accept_3_3 26 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 259
  (Polychromatic418967fa.accept_17_7_3_4_1_8563 24 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 259 (accept_3_3 23 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 259 (Polychromatic418967fa.accept_21_1_12_7_1_3783 22 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 259 (accept_3_3 20 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 259 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 54 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 259
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 259 (accept_3_3 17 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 259 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 259 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 259 (accept_3_3 14 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 259
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 259 (accept_3_3 11 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 259 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 259 (accept_3_3 8 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 259 (Polychromatic418967fa.accept_17_7_3_4_1_8563 7 54 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 259
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 259 (accept_3_3 5 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  259 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 54 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 259 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 259 (accept_3_3 2 54 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 259 (allA_of_3_1 53 53 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 259 (allA_succ_of_accept 51 52 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 259 (accept_3_3 50 52 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 259 (Polychromatic418967fa.accept_16_1_4_3_1_3148
  49 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 259
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 48 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 259 (accept_3_3 47 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 259 (accept_3_3 44 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 259 (Polychromatic418967fa.accept_21_1_10_7_1_11382 43 52 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 259
  (Polychromatic418967fa.accept_15_12_7_4_1_2921 42 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 259 (accept_3_3 41 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 259 (Polychromatic418967fa.accept_15_10_7_4_1_1222 40 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 259 (accept_3_3 38 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 52 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 259
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 259 (accept_3_3 35 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 259 (accept_3_3 32 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 52 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 259
  (Polychromatic418967fa.accept_21_9_10_7_1_383 30 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 259 (accept_3_3 29 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 259 (Polychromatic418967fa.accept_16_12_4_3_1_4295 28 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 259 (accept_3_3 26 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 259 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 52 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 259
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 24 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 259 (accept_3_3 23 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 259 (accept_3_3 20 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 259 (Polychromatic418967fa.accept_18_1_16_7_1_2897 19 52 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 259
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 259 (accept_3_3 17 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 259 (Polychromatic418967fa.accept_19_16_14_12_1_6261 16 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 259 (accept_3_3 14 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 259 (Polychromatic418967fa.accept_19_13_14_12_1_4797 13 52 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 259
  (Polychromatic418967fa.accept_15_12_7_4_1_2921 12 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 259 (accept_3_3 11 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 259 (accept_3_3 8 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 52 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 259
  (Polychromatic418967fa.accept_16_6_4_3_1_2189 6 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 259 (accept_3_3 5 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  259 (Polychromatic418967fa.accept_14_4_10_7_1_1946 4 52 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 259 (accept_3_3 2 52 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 259 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 52 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  259)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 259 (allA_succ_of_accept 50 51 259 (accept_3_3
  50 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 259
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 259 (accept_3_3 47 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 51 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 259 (Polychromatic418967fa.accept_10_5_1_9_1_791
  45 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 259 (accept_3_3 44
  51 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 259
  (Polychromatic418967fa.accept_15_13_6_4_1_1221 43 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 259 (accept_3_3 41 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 39
  51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 259 (accept_3_3 38 51
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 259
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 51 259 (Polychromatic418967fa.accept_21_15_9_7_1_3780 36 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 259 (accept_3_3 35 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 51 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 259 (Polychromatic418967fa.accept_12_9_3_7_1_924
  33 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 259 (accept_3_3 32
  51 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 259
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 51 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 259 (accept_3_3 29 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 51 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 259 (Polychromatic418967fa.accept_21_6_9_7_1_3752
  27 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 259 (accept_3_3 26
  51 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 259
  (Polychromatic418967fa.accept_10_5_1_9_1_791 25 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 51 259 (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 259 (accept_3_3 23 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 51 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 259 (accept_3_3 20 51
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 259
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 51 259 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 259 (accept_3_3 17 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 51 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 259 (Polychromatic418967fa.accept_10_5_1_9_1_791
  15 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 259 (accept_3_3 14
  51 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 259
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 51 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 259 (accept_3_3 11 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 51 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 51 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 259 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 259 (accept_3_3 8 51 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 259 (Polychromatic418967fa.accept_23_7_5_6_1_15762
  7 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 259
  (Polychromatic418967fa.accept_19_6_13_12_1_6220 6 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 259 (accept_3_3 5 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 259 (accept_3_3 2 51 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 51 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 259)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 259 (allA_of_3_1 50 50 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 259
  (allA_succ_of_accept 48 49 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 259 (accept_3_3 47 49 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 259 (Polychromatic418967fa.accept_11_1_5_6_1_397
  45 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 259 (accept_3_3 44
  49 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 259
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 49 259 7 6 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 49 259 (accept_3_3 41 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 259 (Polychromatic418967fa.accept_18_4_13_7_1_5395 40 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 49 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 259 (accept_3_3 38 49 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 259
  (Polychromatic418967fa.accept_16_4_1_3_1_6581 36 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 49 259 7 5 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 49 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 49 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 259 (accept_3_3 32 49 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 259 (Polychromatic418967fa.accept_23_8_3_6_1_15761
  31 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 259 (accept_3_3 29 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49
  259 7 4 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  49 259 (Polychromatic418967fa.accept_17_10_15_4_1_5967 27 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 49 259 (accept_3_3 26 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 49 259 (Polychromatic418967fa.accept_22_3_5_17_1_9702 25 49 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 259 (accept_3_3 23 49 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 49 259 7 3 7 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 49 259 (accept_3_3 20
  49 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 259
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 259 (accept_3_3 17 49 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 259 (Polychromatic418967fa.accept_17_16_15_4_1_8559 16 49 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 49 259 7 2 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 49 259 (Polychromatic418967fa.accept_16_13_1_3_1_2205 13 49 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 259 (accept_3_3 11 49 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 259
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 259 (accept_3_3 8 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 259
  7 1 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 49 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 259 (accept_3_3 5 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  259 (Polychromatic418967fa.accept_16_4_1_3_1_6581 4 49 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 49 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 259 (accept_3_3 2 49 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 259)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 259 (allA_succ_of_accept 47 48 259 (accept_3_3 47 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 48 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 259 (Polychromatic418967fa.accept_21_3_6_7_1_6750 45 48 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 259 (accept_3_3 44 48 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 259 (Polychromatic418967fa.accept_14_1_6_7_1_1936
  43 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 259 (accept_3_3 41 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  48 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 259 (Polychromatic418967fa.accept_18_3_12_7_1_6728 39 48 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 259 (accept_3_3 38 48 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 48 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 259
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 259 (accept_3_3 35 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 48 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 259 (accept_3_3 32 48 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 259
  (Polychromatic418967fa.accept_17_13_14_4_1_2468 30 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 259 (accept_3_3 29 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 48 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 259 (accept_3_3 26 48 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 259 (Polychromatic418967fa.accept_19_6_10_12_1_11771 25 48 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 259 (accept_3_3 23 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 48 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 259 (accept_3_3 20 48 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 259
  (Polychromatic418967fa.accept_17_1_14_4_1_1550 18 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 259 (accept_3_3 17 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 259 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 259 (accept_3_3 14 48 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 259
  (Polychromatic418967fa.accept_21_12_6_7_1_3739 12 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 259 (accept_3_3 11 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 259 (Polychromatic418967fa.accept_17_9_14_4_1_3483 9 48 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 259 (accept_3_3 8 48 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 48 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 259 (accept_3_3 5 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  259 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 48 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 259 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 48 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 259 (accept_3_3 2 48 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 259)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 259 (allA_of_3_1 47 47 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 259 (allA_succ_of_accept 45 46
  259 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 259 (accept_3_3 44 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 46 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 259 (accept_3_3 41 46 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 46 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 259 (accept_3_3 38 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 259 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 46 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 259 (accept_3_3 35 46 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 259 (Polychromatic418967fa.accept_13_8_7_12_1_3637 34 46
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 259 (accept_3_3 32 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 46 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 259 (accept_3_3 29 46 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 46 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 259 (accept_3_3 26 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 46 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 259 (accept_3_3 23 46 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 46 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 259 (accept_3_3 20 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 259 (Polychromatic418967fa.accept_13_6_7_12_1_3504 19 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 259 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 46 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 259 (accept_3_3 17 46 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 46 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 259 (accept_3_3 14 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 46 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 259 (accept_3_3 11 46 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 259 (Polychromatic418967fa.accept_13_10_7_12_1_2782 10 46 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 259 (accept_3_3 8 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  259 (Polychromatic418967fa.accept_17_7_12_4_1_2524 7 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 46 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 46 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 259 (accept_3_3 5 46 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 46 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 46 259 (accept_3_3 2 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46
  259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 259)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 259 (allA_succ_of_accept 44 45 259
  (accept_3_3 44 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 259
  (Polychromatic418967fa.accept_19_5_7_12_1_2252 43 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 259 (accept_3_3 41 45 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 259 (Polychromatic418967fa.accept_12_3_9_7_1_472
  39 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 259 (accept_3_3 38
  45 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 259
  (Polychromatic418967fa.accept_19_18_7_12_1_6148 37 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 45 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 45 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 259 (accept_3_3 35 45 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 45 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 259 (Polychromatic418967fa.accept_13_7_6_12_1_2027
  33 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 259 (accept_3_3 32
  45 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 259
  (Polychromatic418967fa.accept_10_1_5_9_1_157 31 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 45 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 259 (accept_3_3 29 45 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 45 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 259 (Polychromatic418967fa.accept_11_5_1_6_1_774
  27 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 259 (accept_3_3 26
  45 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 259
  (Polychromatic418967fa.accept_14_11_3_7_1_604 25 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 45 259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 45 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 259 (accept_3_3 23 45 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 45 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 259 (Polychromatic418967fa.accept_10_1_5_9_1_157
  21 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 259 (accept_3_3 20
  45 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 259
  (Polychromatic418967fa.accept_27_19_18_16_1_15760 19 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 259 (accept_3_3 17 45 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 259 (accept_3_3 14 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 259 (Polychromatic418967fa.accept_20_13_5_19_1_10110 13 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 259 (Polychromatic418967fa.accept_21_12_3_7_1_14223 12 45 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 259 (accept_3_3 11 45 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 259
  (Polychromatic418967fa.accept_21_9_3_7_1_15759 9 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 259 (accept_3_3 8 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  259 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 259 (accept_3_3 5 45 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 259 (accept_3_3 2 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45
  259 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 45 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 259))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 259 (allA_of_3_1 44 44 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 43 259 (allA_succ_of_accept 42 43 259
  (Polychromatic418967fa.accept_13_3_4_12_1_36 42 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 259 (accept_3_3 41 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 40 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 259 (Polychromatic418967fa.accept_15_9_13_4_1_1209 39 43 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 259 (accept_3_3 38 43 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 259 (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 43
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 259
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 259 (accept_3_3 35 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 34 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 43 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 259 (accept_3_3 32 43 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 259 (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 43
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 259
  (Polychromatic418967fa.accept_16_14_11_3_1_4249 30 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 259 (accept_3_3 29 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 259 (Polychromatic418967fa.accept_13_2_4_12_1_745 28 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 259 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 43 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 259 (accept_3_3 26 43 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 43 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 259
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 259 (accept_3_3 23 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 259 (Polychromatic418967fa.accept_14_8_1_7_1_3725 22 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 259 (Polychromatic418967fa.accept_13_8_4_12_1_2753 21 43 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 259 (accept_3_3 20 43 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 259 (Polychromatic418967fa.accept_17_2_9_4_1_3463 19 43 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 259
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 259 (accept_3_3 17 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 259 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 259 (Polychromatic418967fa.accept_13_2_4_12_1_745 15 43 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 259 (accept_3_3 14 43 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 259 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 43 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 259
  (Polychromatic418967fa.accept_17_12_9_4_1_5982 12 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 259 (accept_3_3 11 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 259 (Polychromatic418967fa.accept_15_9_13_4_1_1209 9 43 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 259 (accept_3_3 8 43 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 43 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 259
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 259 (accept_3_3 5 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 43 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 259 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 43 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 259 (accept_3_3 2 43 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 259 (Polychromatic418967fa.accept_19_1_5_12_1_6249 1 43 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 259)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 259 (allA_succ_of_accept 41 42 259 (accept_3_3 41 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 42 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 259 (accept_3_3 38 42 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 259
  (Polychromatic418967fa.accept_11_3_9_6_1_105 36 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 42 259 7 5 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 42 259 (Polychromatic418967fa.accept_22_12_20_17_1_9621 34 42 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 259 (accept_3_3 32 42 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 31
  42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 259 (accept_3_3 29 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42
  259 7 4 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  42 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 259 (accept_3_3 26 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 42 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 259 (Polychromatic418967fa.accept_15_9_12_4_1_2023 24 42
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 259 (accept_3_3 23 42 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 22
  42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 259 7 3 6 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 259 (accept_3_3 20
  42 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 259
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 42 259 (Polychromatic418967fa.accept_17_1_8_4_1_1519 18 42 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 259 (accept_3_3 17 42 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 42 259 (Polychromatic418967fa.accept_15_1_12_4_1_2022 16 42 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 259
  (Polychromatic418967fa.accept_13_2_3_12_1_735 15 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 42 259 7 2 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 42 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 259 (accept_3_3 11 42 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 10
  42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 42 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 259 (accept_3_3 8 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 42 259
  7 1 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 42 259
  (Polychromatic418967fa.accept_19_6_4_12_1_6193 6 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 259 (accept_3_3 5 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  259 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 42 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 259 (accept_3_3 2 42 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 259)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 259
  (allA_of_3_1 41 41 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 259 (allA_succ_of_accept 39 40 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 259 (accept_3_3 38 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 259 (Polychromatic418967fa.accept_15_6_10_4_1_150 36 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 259 (accept_3_3 35 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 34 40 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 259 (accept_3_3 32 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 259 (Polychromatic418967fa.accept_13_5_1_12_1_740 31 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 259 (accept_3_3 29 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 40 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 259 (accept_3_3 26 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 259 (Polychromatic418967fa.accept_19_6_2_12_1_6136 25 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 259 (accept_3_3 23 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 40 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 259 (accept_3_3 20 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 259 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 259 (accept_3_3 17 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 259 (Polychromatic418967fa.accept_14_2_12_7_1_617 16 40 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 259 (accept_3_3 14 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 259 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 259 (accept_3_3 11 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 40 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 259 (accept_3_3 8 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  259 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 40 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 259 (accept_3_3 5 40 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 259 (Polychromatic418967fa.accept_16_4_8_3_1_4206 4 40 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 259 (accept_3_3 2 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 40 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 259)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 259 (allA_succ_of_accept 38 39 259 (accept_3_3
  38 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 259
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 259 (accept_3_3 35 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 39 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 33
  39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 259 (accept_3_3 32 39
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 39 259 (Polychromatic418967fa.accept_18_12_3_7_1_5373 30 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 259 (accept_3_3 29 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 39 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 259 (Polychromatic418967fa.accept_15_12_9_4_1_3898
  27 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 259 (accept_3_3 26
  39 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 259
  (Polychromatic418967fa.accept_15_10_9_4_1_2924 25 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 259 (accept_3_3 23 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 259 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 259 (accept_3_3 20
  39 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 259
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 39 259 (Polychromatic418967fa.accept_14_4_11_7_1_1234 18 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 259 (accept_3_3 17 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 39 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 259 (accept_3_3 14 39
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 39 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 259 (accept_3_3 11 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 39 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 259 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 259 (accept_3_3 8 39 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 259 (Polychromatic418967fa.accept_19_7_1_12_1_6134
  7 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 259 (accept_3_3 5 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 259 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 259 (accept_3_3 2 39 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 39 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 259))))))))))))))))))))))))))))))))))))))) (allB_succ 38 259
  (allA_of_3_1 38 38 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 259 (allA_succ_of_accept 36 37 259
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 37 259 (accept_3_3 35 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 37 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 37 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 259 (accept_3_3 32 37 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31
  37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 259 (accept_3_3 29 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 259 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 259 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 37 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 259 (accept_3_3 26 37 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 259 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 37
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 259 (accept_3_3 23 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 37 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 259 (accept_3_3 20 37 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 259 (Polychromatic418967fa.accept_14_5_9_7_1_590 19 37 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 259 (accept_3_3 17 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 259 (Polychromatic418967fa.accept_14_2_9_7_1_5633 16 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 37 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 259 (accept_3_3 14 37 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 37 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 259 (accept_3_3 11 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 259 (Polychromatic418967fa.accept_19_9_18_12_1_2286 9 37 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 259 (accept_3_3 8 37 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 259 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 37 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 259 (accept_3_3 5 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 37 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 37 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 259 (accept_3_3 2 37 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 259 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 37 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 259))))))))))))))))))))))))))))))))))))) (allB_succ 36 259
  (allA_succ_of_accept 35 36 259 (accept_3_3 35 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 259 (Polychromatic418967fa.accept_13_8_10_12_1_1337 34 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 36 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 259 (accept_3_3 32 36 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 36 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 259
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 259 (accept_3_3 29 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 259 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 259 (Polychromatic418967fa.accept_14_13_8_7_1_1224 27 36 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 259 (accept_3_3 26 36 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 259 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 36 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 259
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 36 259 (accept_3_3 23 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 259 (Polychromatic418967fa.accept_13_9_10_12_1_2048 22 36 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 259 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 36
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 259 (accept_3_3 20 36 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 259 (Polychromatic418967fa.accept_11_8_3_6_1_1855
  19 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 259
  (Polychromatic418967fa.accept_19_18_17_12_1_4764 18 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 36 259 (accept_3_3 17 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 259 (Polychromatic418967fa.accept_23_16_13_6_1_7584 16 36 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 259 (accept_3_3 14 36 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 259 (Polychromatic418967fa.accept_10_3_6_9_1_779
  13 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 259
  (Polychromatic418967fa.accept_16_12_4_3_1_4295 12 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 259 (accept_3_3 11 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 259 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 259 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 36 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 259 (accept_3_3 8 36 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 259
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 259 (accept_3_3 5 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  259 (Polychromatic418967fa.accept_24_4_12_19_1_12489 4 36 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 36 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 259 (accept_3_3 2 36 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 259 (Polychromatic418967fa.accept_14_1_8_7_1_1253 1 36 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 259)))))))))))))))))))))))))))))))))))) (allB_succ 35
  259 (allA_of_3_1 35 35 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 259 (allA_succ_of_accept 33 34 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 259 (accept_3_3 32 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 259 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 259 (Polychromatic418967fa.accept_13_4_8_12_1_3526 30 34 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 259 (accept_3_3 29 34 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 34 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 259 (accept_3_3 26 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 259 (Polychromatic418967fa.accept_19_5_15_12_1_6273 24 34 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 259 (accept_3_3 23 34 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 259 (Polychromatic418967fa.accept_13_9_8_12_1_2031 22 34
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 259 (accept_3_3 20 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 259 (Polychromatic418967fa.accept_18_1_16_7_1_2897 19 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 34 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 259 (accept_3_3 17 34 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 34 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 259 (accept_3_3 14 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 259 (Polychromatic418967fa.accept_26_12_8_25_1_15758 12 34 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 259 (accept_3_3 11 34 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 259 (Polychromatic418967fa.accept_13_10_8_12_1_2032 10 34
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 259 (accept_3_3 8 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  259 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 34 259 (Polychromatic418967fa.accept_16_6_2_3_1_4223 6 34 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 259 (accept_3_3 5 34 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 34 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 259 (accept_3_3 2 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34
  259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 259)))))))))))))))))))))))))))))))))) (allB_succ 33 259 (allA_succ_of_accept 32 33 259 (accept_3_3 32 33
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 259
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 33 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 33 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 259 (accept_3_3 29 33 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 33 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 259 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 33 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 259 (accept_3_3 26
  33 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 259
  (Polychromatic418967fa.accept_19_6_14_12_1_4811 25 33 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 33 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 33 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 259 (accept_3_3 23 33 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 33 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  33 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 259 (accept_3_3 20 33
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 259
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 33 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 33 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 259 (accept_3_3 17 33 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 33 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 259 (Polychromatic418967fa.accept_12_3_9_7_1_472
  15 33 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 259 (accept_3_3 14
  33 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 259
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 33 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 33 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 259 (accept_3_3 11 33 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 33 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 259 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9
  33 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 259 (accept_3_3 8 33 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 259 (Polychromatic418967fa.accept_15_7_3_4_1_574 7
  33 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 259 (accept_3_3 5 33 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 33 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 259 (accept_3_3 2 33 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 33 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 259))))))))))))))))))))))))))))))))) (allB_succ 32 259
  (allA_of_3_1 32 32 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 259 (allA_succ_of_accept 30 31 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 259 (accept_3_3 29 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 259 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 31 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 259 (accept_3_3 26 31 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 31 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 259 (accept_3_3 23 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 31 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 259 (accept_3_3 20 31 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 259
  (Polychromatic418967fa.accept_10_8_1_9_1_413 18 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 259 (accept_3_3 17 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 259 (Polychromatic418967fa.accept_21_16_10_7_1_3782 16 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 31 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 259 (accept_3_3 14 31 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 259 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 31 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 259
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 259 (accept_3_3 11 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 259 (Polychromatic418967fa.accept_17_9_14_4_1_3483 9 31 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 259 (accept_3_3 8 31 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 259 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 31 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 259 (accept_3_3 5 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  259 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 31 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 31 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 259 (accept_3_3 2 31 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 31 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 259))))))))))))))))))))))))))))))) (allB_succ 30 259
  (allA_succ_of_accept 29 30 259 (accept_3_3 29 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 259 (Polychromatic418967fa.accept_16_11_14_3_1_3140 27 30 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 259 (accept_3_3 26 30 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 259 (accept_3_3 23 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 259 (accept_3_3 20 30 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 30 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 259
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 259 (accept_3_3 17 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 259 (Polychromatic418967fa.accept_13_3_4_12_1_36 16 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 30 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 259 (accept_3_3 14 30 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 259
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 259 (accept_3_3 11 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  30 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 30 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 259 (accept_3_3 8 30 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 30 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 259 (accept_3_3 5 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  259 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 30 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 30 259 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 30 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 259 (accept_3_3 2 30 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 30 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 259)))))))))))))))))))))))))))))) (allB_succ 29 259 (allA_of_3_1
  29 29 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 259 (allA_succ_of_accept 27 28 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 259 (accept_3_3 26 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 28 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 259 (accept_3_3 23 28 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 28 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 28 259 7 3 4 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 28 259 (accept_3_3 20 28 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 259 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 28
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 259
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 259 (accept_3_3 17 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  28 259 (Polychromatic418967fa.accept_13_3_2_12_1_2797 16 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 259 7 2 4 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  28 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 259 (accept_3_3 11 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 259 (accept_3_3 8 28 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 28 259 7 1 4 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 28 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 28 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 259 (accept_3_3 5 28 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 28 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 259 (accept_3_3 2 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28
  259 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 28 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 259)))))))))))))))))))))))))))) (allB_succ 27 259 (allA_succ_of_accept 26 27 259 (accept_3_3 26 27 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 259 (Polychromatic418967fa.accept_19_6_8_12_1_6271
  25 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 259
  (Polychromatic418967fa.accept_13_11_1_12_1_742 24 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 259 (accept_3_3 23 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 259 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 27 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 259 (accept_3_3 20 27 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 259 (Polychromatic418967fa.accept_22_19_5_17_1_9630 19 27
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 259
  (Polychromatic418967fa.accept_10_8_7_9_1_425 18 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 259 (accept_3_3 17 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 259 (Polychromatic418967fa.accept_13_2_1_12_1_1326 15 27 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 259 (accept_3_3 14 27 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 259 (Polychromatic418967fa.accept_21_13_6_7_1_1237 13 27
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 259
  (Polychromatic418967fa.accept_10_2_7_9_1_783 12 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 259 (accept_3_3 11 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 259 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 27 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 259 (accept_3_3 8 27 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 259 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 27 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 259
  (Polychromatic418967fa.accept_14_6_13_7_1_2015 6 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 259 (accept_3_3 5 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 27 259 (Polychromatic418967fa.accept_18_3_9_7_1_1839 3 27 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 259 (accept_3_3 2 27 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 27 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 27 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 259))))))))))))))))))))))))))) (allB_succ 26 259 (allA_of_3_1 26
  26 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 259 (allA_succ_of_accept 24 25 259
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 259 (accept_3_3 23 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 25 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 259 (accept_3_3 20 25 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 259 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 25 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 259 (accept_3_3 17 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 259 (Polychromatic418967fa.accept_19_15_6_12_1_7746 15 25 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 259 (accept_3_3 14 25 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 259 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 25
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 259
  (Polychromatic418967fa.accept_16_12_9_3_1_5363 12 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 259 (accept_3_3 11 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 259 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 25 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 259 (accept_3_3 8 25 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 25 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 259 (accept_3_3 5 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 25 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 25 259 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3 25 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 259 (accept_3_3 2 25 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 25 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 259))))))))))))))))))))))))) (allB_succ 24 259
  (allA_succ_of_accept 23 24 259 (accept_3_3 23 24 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  24 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 24 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 24 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 259 (accept_3_3 20 24 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 259
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 24 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 259 (accept_3_3 17 24 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 259 (Polychromatic418967fa.accept_19_16_5_12_1_6142 16 24 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 259 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 24 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 259 (accept_3_3 14 24 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 24 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 259 (accept_3_3 11 24 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 24 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 259 (Polychromatic418967fa.accept_18_9_6_7_1_6719 9 24 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 259 (accept_3_3 8 24 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 259 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 24 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 259
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 6 24 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 259 (accept_3_3 5 24 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  259 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 24 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 259 (accept_3_3 2 24 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 24 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 259)))))))))))))))))))))))) (allB_succ 23 259 (allA_of_3_1 23 23
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 259 (allA_succ_of_accept 21 22 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 259 (accept_3_3 20 22 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 22 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 259 (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 22 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 259 (accept_3_3 17 22 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 22 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 259 (accept_3_3 14 22 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 22 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 259 (accept_3_3 11 22 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 22 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 259 (accept_3_3 8 22 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  259 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 22 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 22 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 259 (accept_3_3 5 22 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 22 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 259 (accept_3_3 2 22 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 259)))))))))))))))))))))) (allB_succ 21
  259 (allA_succ_of_accept 20 21 259 (accept_3_3 20 21 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 21 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 259 (accept_3_3 17 21 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 21 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 21 259 7 2 3 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 21 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 21 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 21 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 259 (accept_3_3 11 21 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  21 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 259
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 21 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 259 (accept_3_3 8 21 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 259
  7 1 3 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 21 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 259 (accept_3_3 5 21 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 21 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 259 (accept_3_3 2 21 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 21 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 259))))))))))))))))))))) (allB_succ 20 259 (allA_of_3_1 20 20
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 259 (allA_succ_of_accept 18 19 259
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 19 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 259 (accept_3_3 17 19 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 259 (Polychromatic418967fa.accept_14_2_5_7_1_3767 16 19 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 19 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 259 (accept_3_3 14 19 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 19 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 259 (accept_3_3 11 19 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 259 (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 19 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 259 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 19 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 259 (accept_3_3 8 19 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 259 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 19 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 19 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 259 (accept_3_3 5 19 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 19 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 19 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 259 (accept_3_3 2 19 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 259 (Polychromatic418967fa.accept_21_1_19_7_1_1218 1 19 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 259))))))))))))))))))) (allB_succ 18 259 (allA_succ_of_accept 17
  18 259 (accept_3_3 17 18 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 259
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 18 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 259 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 18 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 259 (accept_3_3 14 18 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 259 (Polychromatic418967fa.accept_11_1_7_6_1_378
  12 18 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 259 (accept_3_3 11
  18 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 259
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 18 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 18 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 259 (accept_3_3 8 18 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 18 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 18 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 259 (Polychromatic418967fa.accept_13_6_5_12_1_307 6
  18 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 259 (accept_3_3 5 18 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 4
  18 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 259
  (Polychromatic418967fa.accept_14_3_4_7_1_175 3 18 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 259 (accept_3_3 2 18 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18
  259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 259)))))))))))))))))) (allB_succ 17 259 (allA_of_3_1 17 17 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 259 (allA_succ_of_accept 15 16 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 259 (accept_3_3 14 16 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 16 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 259
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 16 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 259 (accept_3_3 11 16 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 259 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 16 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 259 (accept_3_3 8 16 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 259 (Polychromatic418967fa.accept_19_7_16_12_1_10556 7 16 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 259
  (Polychromatic418967fa.accept_19_6_16_12_1_6118 6 16 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 259 (accept_3_3 5 16 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  259 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 16 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 16 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 259 (accept_3_3 2 16 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 16 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 259)))))))))))))))) (allB_succ 15 259
  (allA_succ_of_accept 14 15 259 (accept_3_3 14 15 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  15 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 15 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 15 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 259 (accept_3_3 11 15 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 15 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 15 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 259 (accept_3_3 8 15 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  259 (Polychromatic418967fa.accept_16_7_15_3_1_1302 7 15 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 15 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 259 (accept_3_3 5 15 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 15 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 259 (accept_3_3 2 15 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15
  259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 15 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 259))))))))))))))) (allB_succ 14 259 (allA_of_3_1 14 14 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 13 259 (allA_succ_of_accept 12 13 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 13 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 13 259 (accept_3_3 11 13 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 259
  (Polychromatic418967fa.accept_15_9_13_4_1_1209 9 13 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 13 259 (accept_3_3 8 13 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13
  259 (Polychromatic418967fa.accept_22_7_13_17_1_9708 7 13 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 13 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 259 (accept_3_3 5 13 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 13 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 13 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 259 (accept_3_3 2 13 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13
  259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 259))))))))))))) (allB_succ 12 259 (allA_succ_of_accept 11 12 259 (accept_3_3 11 12 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 12 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 259
  (Polychromatic418967fa.accept_14_9_12_7_1_597 9 12 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 12 259 (accept_3_3 8 12 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12
  259 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 12 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 12 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 259 (accept_3_3 5 12 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 12 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 12 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 259 (Polychromatic418967fa.accept_18_3_12_7_1_6728
  3 12 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 259 (accept_3_3 2 12
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1
  12 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 259)))))))))))) (allB_succ 11 259
  (allA_of_3_1 11 11 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 259 (allA_succ_of_accept 9 10 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 259 (accept_3_3 8 10 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  259 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 10 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 10 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 10 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 259 (accept_3_3 5 10 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 10 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 10 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 10 259 (accept_3_3 2 10 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10
  259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 259)))))))))) (allB_succ 9 259 (allA_succ_of_accept 8 9 259 (accept_3_3 8 9 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 259 (Polychromatic418967fa.accept_16_7_9_3_1_1324 7 9 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 259 (accept_3_3 5 9 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 259
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 9 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 259 (accept_3_3 2 9 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 259 (Polychromatic418967fa.accept_19_1_9_12_1_6207 1 9 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 259))))))))) (allB_succ 8 259 (allA_of_3_1 8 8 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 259 (allA_succ_of_accept 6 7 259
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 7 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 259 (accept_3_3 5 7 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 259
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 7 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 259 (Polychromatic418967fa.accept_15_3_7_4_1_1225 3 7 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 259 (accept_3_3 2 7 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 7 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 259))))))) (allB_succ 6 259 (allA_succ_of_accept 5 6 259
  (accept_3_3 5 6 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 259
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 6 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 6 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 259 (accept_3_3 2 6 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 259)))))) (allB_succ 5 259 (allA_of_3_1 5 5 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 259 (allA_succ_of_accept 3 4 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 259 (accept_3_3 2 4 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 259
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 259)))) (allB_succ 3 259 (allA_succ_of_accept 2 3 259 (accept_3_3 2 3 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 3 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 259))) (allB_succ 2 259 (allA_of_3_1 2 2 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


