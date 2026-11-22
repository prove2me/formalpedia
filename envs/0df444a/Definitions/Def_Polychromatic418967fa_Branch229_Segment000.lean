-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch229_Segment000
-- name    : Polychromatic418967fa_Branch229_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:36:43.865175+00:00
-- url     : https://prove2.me/theorems/30b3ba44-deae-4b0b-9bd2-b8a988b2dde0
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

def Polychromatic418967fa.branch_229_segment_000 : allB 123 229 :=
  allB_succ' 108 122 229 (Eq.refl Bool.true) (allA_of_3_1 108 122 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 109 121 229 (Eq.refl Bool.true) (allA_succ_of_accept 108 121 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 108 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 121 229 (accept_3_3 107 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 121 229 (Polychromatic418967fa.accept_21_1_16_19_1_3134 106 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 105 121 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 121 229 (accept_3_3 104 121 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 121 229
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 103 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 121 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 102 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 229 (accept_3_3 101 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 100 121
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 229
  (Polychromatic418967fa.accept_19_4_7_1_1_1683 99 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 229 (accept_3_3 98 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 229 (Polychromatic418967fa.accept_16_1_9_5_1_5443 97 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 229 (Polychromatic418967fa.accept_17_11_2_8_1_7569 96 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 229 (accept_3_3 95 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 94 121 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 229
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 93 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 229 (accept_3_3 92 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 229 (Polychromatic418967fa.accept_14_7_9_5_1_529 91 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 229 (Polychromatic418967fa.accept_13_12_4_8_1_1120 90 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 229 (accept_3_3 89 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 121 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 87 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 229 (accept_3_3 86 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 85 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 229 (accept_3_3 83 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 82 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 81 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 229 (accept_3_3 80 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 229 (Polychromatic418967fa.accept_17_11_2_8_1_7569 79 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 78 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 229 (accept_3_3 77 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 76 121 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 229
  (Polychromatic418967fa.accept_10_5_1_9_1_791 75 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 229 (accept_3_3 74 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 229 (accept_3_3 71 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 229 (Polychromatic418967fa.accept_19_13_7_1_1_5379 70 121
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 229
  (Polychromatic418967fa.accept_19_12_7_1_1_5400 69 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 229 (accept_3_3 68 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 229 (accept_3_3 65 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 229 (Polychromatic418967fa.accept_13_12_4_8_1_1120 64 121 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 229
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 229 (accept_3_3 62 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 229 (Polychromatic418967fa.accept_13_9_4_8_1_1752 61 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 229 (accept_3_3 59 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 58 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 229
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 57 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 229 (accept_3_3 56 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 55 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 229 (Polychromatic418967fa.accept_37_17_10_7_1_13699 54 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 229 (accept_3_3 53 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 121 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 229
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 51 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 229 (accept_3_3 50 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 229 (Polychromatic418967fa.accept_13_10_4_8_1_2570 49 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 229 (accept_3_3 47 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 121 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 229 (accept_3_3 44 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 229 (Polychromatic418967fa.accept_16_11_9_5_1_4412 43 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 229 (accept_3_3 41 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 229 (Polychromatic418967fa.accept_19_2_7_1_1_2808 40 121
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 229 (accept_3_3 38 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 229 (Polychromatic418967fa.accept_13_11_4_8_1_1098 37 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 229 (accept_3_3 35 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 229 (Polychromatic418967fa.accept_21_13_16_19_1_1828 34 121 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 229
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 33 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 229 (accept_3_3 32 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 229 (Polychromatic418967fa.accept_16_14_9_5_1_4388 30 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 229 (accept_3_3 29 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 121 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 229
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 27 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 229 (accept_3_3 26 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 229 (accept_3_3 23 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 229
  (Polychromatic418967fa.accept_14_7_9_5_1_529 21 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 229 (accept_3_3 20 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 229 (Polychromatic418967fa.accept_22_19_11_9_1_9028 19 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 229 (accept_3_3 17 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 229 (Polychromatic418967fa.accept_17_16_2_8_1_7625 16 121 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 229
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 229 (accept_3_3 14 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 229 (Polychromatic418967fa.accept_16_13_9_5_1_3302 13 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 229 (accept_3_3 11 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 229
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 229 (accept_3_3 8 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 229 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 229 (Polychromatic418967fa.accept_19_6_7_1_1_2805 6 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 229 (accept_3_3 5 121 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 121 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 229 (accept_3_3 2 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 229 (Polychromatic418967fa.accept_16_1_9_5_1_5443 1 121 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 120 229 (Eq.refl Bool.true) (allA_succ_of_accept 109 120 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 109 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 120 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 108 120 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 229 (accept_3_3 107 120 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 120 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 106 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 120 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 105 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 120 229 (accept_3_3 104 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 120 229 (Polychromatic418967fa.accept_26_25_16_21_1_13698 103 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 120 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 102 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 120 229 (accept_3_3 101 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 100 120
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 229
  (Polychromatic418967fa.accept_16_3_8_5_1_6790 99 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 120 229 (accept_3_3 98 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 120 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 97 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 120 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 96 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 120 229 (accept_3_3 95 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 94 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 229
  (Polychromatic418967fa.accept_16_13_8_5_1_3298 93 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 120 229 (accept_3_3 92 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 120 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 120 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 120 229 (accept_3_3 89 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 88 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 87 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 120 229 (accept_3_3 86 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 120 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 85 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 120 229 (Polychromatic418967fa.accept_16_4_8_5_1_3317 84 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 120 229 (accept_3_3 83 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 120 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 81 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 120 229 (accept_3_3 80 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 120 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 120 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 229 (accept_3_3 77 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 229
  (Polychromatic418967fa.accept_16_11_8_5_1_4366 75 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 120 229 (accept_3_3 74 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 120 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 120 229 (Polychromatic418967fa.accept_13_7_3_8_1_1750 72 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 120 229 (accept_3_3 71 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 120 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 120 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 120 229 (accept_3_3 68 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 120 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 120 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 120 229 (accept_3_3 65 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 229
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 120 229 (accept_3_3 62 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 120 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 120 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 120 229 (accept_3_3 59 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 229 (Polychromatic418967fa.accept_17_7_1_8_1_6280 58 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 229
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 57 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 120 229 (accept_3_3 56 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 120 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 120 229 (Polychromatic418967fa.accept_21_12_15_19_1_10743 54 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 120 229 (accept_3_3 53 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 120 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 120 229 (accept_3_3 50 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 120 229 (Polychromatic418967fa.accept_19_11_6_1_1_2826 49 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 120 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 229 (accept_3_3 47 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 120 229 (accept_3_3 44 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 120 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 120 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 120 229 (accept_3_3 41 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 229 (Polychromatic418967fa.accept_19_2_6_1_1_9729 40 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 120 229 (accept_3_3 38 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 120 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 120 229 (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 120 229 (accept_3_3 35 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 120 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 120 229 (accept_3_3 32 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 120 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 120 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 120 229 (accept_3_3 29 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 120 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 120 229 (accept_3_3 26 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 120 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 120 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 229 (accept_3_3 23 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 229 (Polychromatic418967fa.accept_13_9_3_8_1_573 22 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 229
  (Polychromatic418967fa.accept_17_4_1_8_1_5070 21 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 120 229 (accept_3_3 20 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 120 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 120 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 229 (accept_3_3 17 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 120 229 (accept_3_3 14 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 120 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 120 229 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 229 (accept_3_3 11 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 120 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 229
  (Polychromatic418967fa.accept_13_9_3_8_1_573 9 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 120 229 (accept_3_3 8 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  120 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 120 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 229 (accept_3_3 5 120 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 120 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 120 229 (accept_3_3 2 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  120 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 120 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 120
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 119 229 (Eq.refl Bool.true) (allA_of_3_1 111 119 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 112 118 229 (Eq.refl Bool.true) (allA_succ_of_accept 111 118 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 111 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 118 229 (accept_3_3 110 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 118 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 109 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 118 229 (Polychromatic418967fa.accept_25_8_18_4_1_13697 108 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 118 229 (accept_3_3 107 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 118 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 106 118
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 118 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 105 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 118 229 (accept_3_3 104 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 118 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 118 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 102 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 118 229 (accept_3_3 101 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 118 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 100 118
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 118 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 99 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 118 229 (accept_3_3 98 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 118 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 118 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 118 229 (accept_3_3 95 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 118 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 94 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 118 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 118 229 (accept_3_3 92 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 118 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 118 229 (Polychromatic418967fa.accept_13_12_1_8_1_1779 90 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 118 229 (accept_3_3 89 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 118 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 118 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 118 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 87 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 118 229 (accept_3_3 86 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 118 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 85 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 118 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 118 229 (accept_3_3 83 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 118 229 (Polychromatic418967fa.accept_17_14_16_8_1_3861 82 118 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 118 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 118 229 (accept_3_3 80 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 118 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 118 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 118 229 (accept_3_3 77 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 118 229 (Polychromatic418967fa.accept_11_10_8_9_1_492 76 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 118 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 118 229 (accept_3_3 74 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 118 229 (Polychromatic418967fa.accept_18_1_10_13_1_500 73 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 118 229 (Polychromatic418967fa.accept_13_7_1_8_1_1778 72 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 118 229 (accept_3_3 71 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 118 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 118 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 118 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 118 229 (accept_3_3 68 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 118 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 118 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 118 229 (accept_3_3 65 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 118 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 118 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 118 229 (accept_3_3 62 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 118 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 118 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 118 229 (accept_3_3 59 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 118 229 (Polychromatic418967fa.accept_13_6_1_8_1_1116 58 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 118 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 118 229 (accept_3_3 56 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 118 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 118 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 118 229 (accept_3_3 53 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 118 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 118 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 118 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 118 229 (accept_3_3 50 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 118 229 (Polychromatic418967fa.accept_16_1_6_5_1_4385 49 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 118 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 118 229 (accept_3_3 47 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 118 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 118 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 118 229 (accept_3_3 44 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 118 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 118 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 118 229 (accept_3_3 41 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 118 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 118 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 118 229 (accept_3_3 38 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 118 229 (Polychromatic418967fa.accept_10_7_8_9_1_785 37 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 118 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 118 229 (accept_3_3 35 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 118 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 118 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 118 229 (accept_3_3 32 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 118 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 118 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 118 229 (accept_3_3 29 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 118 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 118 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 118 229 (accept_3_3 26 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 118 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 118 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 118 229 (accept_3_3 23 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 118 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 118 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 118 229 (accept_3_3 20 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 118 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 118 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 229 (accept_3_3 17 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 118 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 118 229 (accept_3_3 14 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 118 229 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 118 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 229 (accept_3_3 11 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 229 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 118 229 (accept_3_3 8 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  118 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 118 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 229 (accept_3_3 5 118 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 118 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 118 229 (accept_3_3 2 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  118 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 118 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 118
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 117 229 (Eq.refl Bool.true) (allA_succ_of_accept 112 117 229
  (Polychromatic418967fa.accept_6_4_3_1_1_57 112 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 117 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 111 117 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 229 (accept_3_3 110 117 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 117 229 (Polychromatic418967fa.accept_21_4_12_19_1_4513 109 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 229
  (Polychromatic418967fa.accept_10_8_7_9_1_425 108 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 117 229 (accept_3_3 107 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 106 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 117 229 (Polychromatic418967fa.accept_19_10_3_1_1_8312 105 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 229 (accept_3_3 104 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 229 (Polychromatic418967fa.accept_22_15_7_9_1_9053 103
  117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 229
  (Polychromatic418967fa.accept_10_2_7_9_1_783 102 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 117 229 (accept_3_3 101 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 117 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 99 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 229 (accept_3_3 98 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 229 (Polychromatic418967fa.accept_15_7_12_4_1_1236 97 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 229
  (Polychromatic418967fa.accept_18_6_9_13_1_3320 96 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 117 229 (accept_3_3 95 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 117 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 93 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 229 (accept_3_3 92 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 229 (Polychromatic418967fa.accept_15_1_12_4_1_2022 91 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 229
  (Polychromatic418967fa.accept_11_2_7_9_1_890 90 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 117 229 (accept_3_3 89 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 117 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 87 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 229 (accept_3_3 86 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 229 (Polychromatic418967fa.accept_21_1_12_19_1_7721 85 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 229
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 84 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 117 229 (accept_3_3 83 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 117 229 (Polychromatic418967fa.accept_17_13_15_8_1_3860 81 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 229 (accept_3_3 80 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 229 (Polychromatic418967fa.accept_11_2_7_9_1_890 79 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 229
  (Polychromatic418967fa.accept_10_8_7_9_1_425 78 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 117 229 (accept_3_3 77 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 117 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 75 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 229 (accept_3_3 74 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 229 (Polychromatic418967fa.accept_19_16_3_1_1_5389 73 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 229
  (Polychromatic418967fa.accept_10_2_7_9_1_783 72 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 117 229 (accept_3_3 71 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 117 229 (Polychromatic418967fa.accept_15_9_12_4_1_2023 69 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 229 (accept_3_3 68 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 229 (Polychromatic418967fa.accept_15_7_12_4_1_1236 67 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 229
  (Polychromatic418967fa.accept_20_6_17_9_1_7975 66 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 117 229 (accept_3_3 65 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 117 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 63 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 229 (accept_3_3 62 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 229 (Polychromatic418967fa.accept_15_1_12_4_1_2022 61 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 229
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 117 229 (accept_3_3 59 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 117 229 (Polychromatic418967fa.accept_11_2_7_9_1_890 57 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 229 (accept_3_3 56 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 229 (Polychromatic418967fa.accept_19_17_3_1_1_4056 55 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 229
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 54 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 117 229 (accept_3_3 53 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 117 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 229 (accept_3_3 50 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 229
  (Polychromatic418967fa.accept_10_8_7_9_1_425 48 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 117 229 (accept_3_3 47 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 117 229 (Polychromatic418967fa.accept_26_19_13_21_1_13686 45 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 229 (accept_3_3 44 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 229 (Polychromatic418967fa.accept_19_5_3_1_1_4055 43 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 229
  (Polychromatic418967fa.accept_10_2_7_9_1_783 42 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 229 (accept_3_3 41 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 117 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 229 (accept_3_3 38 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 229 (Polychromatic418967fa.accept_15_7_12_4_1_1236 37 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 229
  (Polychromatic418967fa.accept_19_17_3_1_1_4056 36 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 117 229 (accept_3_3 35 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 229 (Polychromatic418967fa.accept_26_7_13_21_1_13696 33 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 229 (accept_3_3 32 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 229 (Polychromatic418967fa.accept_15_1_12_4_1_2022 31 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 229
  (Polychromatic418967fa.accept_17_13_15_8_1_3860 30 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 229 (accept_3_3 29 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 229 (accept_3_3 26 117
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 229
  (Polychromatic418967fa.accept_19_6_3_1_1_2824 25 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 117 229 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 117 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 229 (accept_3_3 23 117 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 117 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 229
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 21 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 117 229 (accept_3_3 20 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 117 229 (Polychromatic418967fa.accept_23_19_2_22_1_13695 19 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 229 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 229 (accept_3_3 17 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 229 (accept_3_3 14 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 117 229 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 229 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 229 (accept_3_3 11 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 117 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 229
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 229 (accept_3_3 8 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  117 229 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 229 (Polychromatic418967fa.accept_17_6_15_8_1_1714 6 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 229 (accept_3_3 5 117 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 229 (accept_3_3 2 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 229 (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 117 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 116 229 (Eq.refl Bool.true) (allA_of_3_1 114 116 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 115 229 (allA_succ_of_accept 114 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 114 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 229 (accept_3_3 113 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 115 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 112 115
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 111 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 115 229 (accept_3_3 110 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 115 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 109 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 115 229 (Polychromatic418967fa.accept_13_4_11_8_1_1768 108 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 115 229 (accept_3_3 107 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 106 115 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 115 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 105 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 115 229 (accept_3_3 104 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 115 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 103 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 115 229 (accept_3_3 101 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 115 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 100 115
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 115 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 99 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 115 229 (accept_3_3 98 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 115 229 (Polychromatic418967fa.accept_13_6_11_8_1_1111 97 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 115 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 115 229 (accept_3_3 95 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 93 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 115 229 (accept_3_3 92 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 115 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 115 229 (accept_3_3 89 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 229 (Polychromatic418967fa.accept_13_10_11_8_1_1770 88 115 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 87 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 229 (accept_3_3 86 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 115 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 115 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 229 (accept_3_3 83 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 229
  (Polychromatic418967fa.accept_10_1_5_9_1_157 81 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 115 229 (accept_3_3 80 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 115 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 79 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 229 (accept_3_3 77 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 115 229 (Polychromatic418967fa.accept_10_6_5_9_1_1233 76 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 75 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 115 229 (accept_3_3 74 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 115 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 115 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 229 (accept_3_3 71 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 115 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 229 (accept_3_3 68 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 67 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 229 (accept_3_3 65 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 115 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 229
  (Polychromatic418967fa.accept_20_3_15_9_1_6456 63 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 115 229 (accept_3_3 62 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 115 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 115 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 229 (accept_3_3 59 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 229 (accept_3_3 56 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 115 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 229 (accept_3_3 53 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 52 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 115 229 (accept_3_3 50 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 115 229 (Polychromatic418967fa.accept_13_10_11_8_1_1770 49 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 229 (accept_3_3 47 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 229
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 45 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 229 (accept_3_3 44 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 229 (accept_3_3 41 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 229 (accept_3_3 38 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 229 (accept_3_3 35 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 229 (accept_3_3 32 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 229 (accept_3_3 29 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 229
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 229 (accept_3_3 26 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 229 (Polychromatic418967fa.accept_20_5_15_9_1_9446 25 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 229 (accept_3_3 23 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 229 (accept_3_3 20 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 229 (accept_3_3 17 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 229 (accept_3_3 14 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 229 (accept_3_3 11 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 229 (accept_3_3 8 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 229 (accept_3_3 5 115 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 229 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 115 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 229 (accept_3_3 2 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 115 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 229 (allA_succ_of_accept 113 114 229 (accept_3_3 113 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 114 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 112 114 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 114 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 114
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 229 (accept_3_3 110 114
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 114 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 109 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 114 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 108 114 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 229 (accept_3_3 107 114 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 114 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 106 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 229
  (Polychromatic418967fa.accept_10_5_4_9_1_420 105 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 114 229 (accept_3_3 104 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 114 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 114 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 102 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 229 (accept_3_3 101 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 100 114
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 99 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 114 229 (accept_3_3 98 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 114 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 97 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 114 229 (Polychromatic418967fa.accept_13_5_10_8_1_1127 96 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 229 (accept_3_3 95 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 94 114 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 114 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 93 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 114 229 (accept_3_3 92 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 114 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 114 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 90 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 114 229 (accept_3_3 89 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 114 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 87 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 114 229 (accept_3_3 86 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 114 229 (Polychromatic418967fa.accept_10_5_4_9_1_420 85 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 114 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 114 229 (accept_3_3 83 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 114 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 81 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 114 229 (accept_3_3 80 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 114 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 114 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 78 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 114 229 (accept_3_3 77 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 229 (Polychromatic418967fa.accept_13_11_10_8_1_1804 76 114
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 114 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 114 229 (accept_3_3 74 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 114 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 114 229 (Polychromatic418967fa.accept_13_7_10_8_1_567 72 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 114 229 (accept_3_3 71 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 114 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 229
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 69 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 114 229 (accept_3_3 68 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 114 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 114 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 114 229 (accept_3_3 65 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 114 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 114 229 (accept_3_3 62 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 114 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 114 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 114 229 (accept_3_3 59 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 114 229 (accept_3_3 56 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 114 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 114 229 (Polychromatic418967fa.accept_13_2_10_8_1_1126 54 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 229 (accept_3_3 53 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 114 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 114 229 (accept_3_3 50 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 114 229 (Polychromatic418967fa.accept_14_7_2_5_1_4528 49 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 114 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 229 (accept_3_3 47 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 114 229 (accept_3_3 44 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 114 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 114 229 (Polychromatic418967fa.accept_15_12_9_4_1_3898 42 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 229 (accept_3_3 41 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 229 (Polychromatic418967fa.accept_15_10_9_4_1_2924 40 114
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 114 229 (accept_3_3 38 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 114 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 114 229 (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 229 (accept_3_3 35 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 114 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 229
  (Polychromatic418967fa.accept_10_3_4_9_1_15 33 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 114 229 (accept_3_3 32 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 114 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 114 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 229 (accept_3_3 29 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 114 229 (accept_3_3 26 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 114 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 114 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 229 (accept_3_3 23 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 229 (Polychromatic418967fa.accept_17_5_12_8_1_6304 22 114 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 114 229 (accept_3_3 20 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 114 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 114 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 229 (accept_3_3 17 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 114 229 (accept_3_3 14 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 114 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 114 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 229 (accept_3_3 11 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 229
  (Polychromatic418967fa.accept_18_9_6_13_1_4499 9 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 114 229 (accept_3_3 8 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  114 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 114 229 (Polychromatic418967fa.accept_15_6_9_4_1_1227 6 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 229 (accept_3_3 5 114 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 114 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 114 229 (accept_3_3 2 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  114 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 114 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 114
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 229 (allA_of_3_1 113 113 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 229
  (allA_succ_of_accept 111 112 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 112 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 112 229 (accept_3_3 110 112 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 112 229 (Polychromatic418967fa.accept_19_14_17_1_1_2788 109 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 112 229
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 108 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 112 229 (accept_3_3 107 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 112 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 106 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 112 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 112 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 112 229 (accept_3_3 104 112 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 112 229 (Polychromatic418967fa.accept_11_4_2_9_1_496 103 112 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 112 229
  (Polychromatic418967fa.accept_15_12_7_4_1_2921 102 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 112 229 (accept_3_3 101 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 112 229 (Polychromatic418967fa.accept_15_10_7_4_1_1222 100 112 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 112 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 99
  112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 112 229 (accept_3_3 98
  112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 112 229
  (Polychromatic418967fa.accept_10_7_2_9_1_775 97 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 112 229 (Polychromatic418967fa.accept_21_12_7_19_1_10736 96 112 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 112 229 (accept_3_3 95 112 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 112 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 94 112 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 112 229 (accept_3_3 92 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 112 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 91 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 112 229 (Polychromatic418967fa.accept_19_14_17_1_1_2788 90 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 112 229 (accept_3_3 89 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 112 229 (Polychromatic418967fa.accept_21_4_7_19_1_13687 88 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 112 229 (accept_3_3 86 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 112 229 (Polychromatic418967fa.accept_15_10_7_4_1_1222 85 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 112 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 84 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 112 229 (accept_3_3 83 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 112 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 82 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 112 229 (accept_3_3 80 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 112 229 (Polychromatic418967fa.accept_18_7_4_13_1_3315 79 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 112 229 (Polychromatic418967fa.accept_15_3_7_4_1_1225 78 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 112 229 (accept_3_3 77 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 112 229 (Polychromatic418967fa.accept_21_13_7_19_1_4505 76 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 112 229 (accept_3_3 74 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 112 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 73 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 112 229 (Polychromatic418967fa.accept_15_12_7_4_1_2921 72 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 112 229 (accept_3_3 71 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 112 229 (Polychromatic418967fa.accept_11_4_2_9_1_496 70 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 112 229 (accept_3_3 68 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 112 229 (Polychromatic418967fa.accept_10_7_2_9_1_775 67 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 112 229 (Polychromatic418967fa.accept_17_15_10_8_1_1708 66 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 229 (accept_3_3 65 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 112 229 (Polychromatic418967fa.accept_18_10_4_13_1_3296 64 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 112 229 (accept_3_3 62 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 112 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 61 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 112 229 (Polychromatic418967fa.accept_19_3_17_1_1_781 60 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 229 (accept_3_3 59 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 112 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 229 (accept_3_3 56 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 229 (Polychromatic418967fa.accept_15_10_7_4_1_1222 55 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 229 (Polychromatic418967fa.accept_19_16_17_1_1_4011 54 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 229 (accept_3_3 53 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 229 (Polychromatic418967fa.accept_19_14_17_1_1_2788 52 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 229 (accept_3_3 50 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 229 (Polychromatic418967fa.accept_17_15_10_8_1_1708 49 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 229 (Polychromatic418967fa.accept_11_4_2_9_1_496 48 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 229 (accept_3_3 47 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 229 (accept_3_3 44 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 229 (Polychromatic418967fa.accept_18_7_4_13_1_3315 43 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 229 (Polychromatic418967fa.accept_15_12_7_4_1_2921 42 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 229 (accept_3_3 41 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 229 (accept_3_3 38 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 229 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 229 (Polychromatic418967fa.accept_17_2_10_8_1_7691 36 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 229 (accept_3_3 35 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 229 (accept_3_3 32 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 229 (Polychromatic418967fa.accept_21_9_7_19_1_9187 30 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 229 (accept_3_3 29 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 229 (Polychromatic418967fa.accept_18_10_4_13_1_3296 28 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 229 (accept_3_3 26 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 229 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 229 (Polychromatic418967fa.accept_25_24_12_4_1_13694 24 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 229 (accept_3_3 23 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 229 (accept_3_3 20 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 229 (Polychromatic418967fa.accept_17_2_10_8_1_7691 19 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 229 (accept_3_3 17 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 229 (Polychromatic418967fa.accept_19_16_17_1_1_4011 16 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 229 (accept_3_3 14 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 229 (Polychromatic418967fa.accept_21_13_7_19_1_4505 13 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 112 229 (Polychromatic418967fa.accept_15_12_7_4_1_2921 12 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 229 (accept_3_3 11 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 112
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 229 (accept_3_3 8 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 229 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 229 (Polychromatic418967fa.accept_24_6_16_13_1_6762 6 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 229 (accept_3_3 5 112 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 229 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 112 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 229 (accept_3_3 2 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 112 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 229 (allA_succ_of_accept 110 111 229 (accept_3_3 110 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 109 111 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 108 111
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 229 (accept_3_3 107 111
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 106 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 111 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 105 111 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 229 (accept_3_3 104 111 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 111 229 (Polychromatic418967fa.accept_13_12_7_8_1_1104 103 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 111 229 (accept_3_3 101 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 111 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 111 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 99 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 229 (accept_3_3 98 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 97 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 96 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 111 229 (accept_3_3 95 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 111 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 111 229 (Polychromatic418967fa.accept_12_9_3_1_1_303 93 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 229 (accept_3_3 92 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 111 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 90 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 111 229 (accept_3_3 89 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 111 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 111 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 229 (accept_3_3 86 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 85 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 229
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 84 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 229 (accept_3_3 83 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 111 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 111 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 229 (accept_3_3 80 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 229 (accept_3_3 77 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 75 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 229 (accept_3_3 74 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 111 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 229
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 111 229 (accept_3_3 71 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 111 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 229 (accept_3_3 68 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 229 (accept_3_3 65 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 229 (Polychromatic418967fa.accept_18_9_3_13_1_5905 63 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 229 (accept_3_3 62 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 111 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 229 (accept_3_3 59 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 229 (accept_3_3 56 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 229 (accept_3_3 53 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 229 (accept_3_3 50 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 229 (Polychromatic418967fa.accept_13_10_7_8_1_1794 49 111 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 229
  (Polychromatic418967fa.accept_10_8_1_9_1_413 48 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 229 (accept_3_3 47 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 229 (accept_3_3 44 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 111 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 229 (accept_3_3 41 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 229 (accept_3_3 38 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 229 (accept_3_3 35 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 229 (accept_3_3 32 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 229 (Polychromatic418967fa.accept_24_7_15_13_1_8570 31 111 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 229 (accept_3_3 29 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 229 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 229 (accept_3_3 26 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 111 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 229 (accept_3_3 23 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 229 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 229 (accept_3_3 20 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 111 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 229 (accept_3_3 17 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 229 (accept_3_3 14 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 229 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 111 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 229
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 229 (accept_3_3 11 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 229 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 229 (accept_3_3 8 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 229 (accept_3_3 5 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 229 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 229 (accept_3_3 2 111 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 111 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 229 (allA_of_3_1 110 110 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 229
  (allA_succ_of_accept 108 109 229 (Polychromatic418967fa.accept_19_13_14_1_1_3996 108 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 229 (accept_3_3 107 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 106 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 105 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 229 (accept_3_3 104 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 229 (Polychromatic418967fa.accept_13_12_5_8_1_1101 103 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 109 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 102 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 229 (accept_3_3 101 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 100 109
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 99 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 229 (accept_3_3 98 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 97 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 229 (accept_3_3 95 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 229 (Polychromatic418967fa.accept_13_3_5_8_1_1099 94 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 93 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 229 (accept_3_3 92 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 229 (Polychromatic418967fa.accept_19_15_14_1_1_8297 91 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 90 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 229 (accept_3_3 89 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 87 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 229 (accept_3_3 86 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 229 (accept_3_3 83 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 229 (Polychromatic418967fa.accept_16_2_13_5_1_2257 82 109 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 229
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 81 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 229 (accept_3_3 80 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 229 (accept_3_3 77 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 75 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 229 (accept_3_3 74 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 229 (Polychromatic418967fa.accept_16_9_13_5_1_2238 73 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 229 (accept_3_3 71 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 229 (accept_3_3 68 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 229 (Polychromatic418967fa.accept_11_1_10_9_1_871 67 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 229 (accept_3_3 65 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 229
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 229 (accept_3_3 62 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 229 (accept_3_3 59 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 229 (accept_3_3 56 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 229 (Polychromatic418967fa.accept_21_12_4_19_1_4526 54 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 229 (accept_3_3 53 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 109 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 229 (accept_3_3 50 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 229 (Polychromatic418967fa.accept_13_10_5_8_1_2555 49 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 229 (accept_3_3 47 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 229 (Polychromatic418967fa.accept_18_10_1_13_1_2192 46 109 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 229
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 229 (accept_3_3 44 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 229 (accept_3_3 41 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 229 (Polychromatic418967fa.accept_13_1_5_8_1_207 40 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 229 (accept_3_3 38 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 229 (accept_3_3 35 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 229 (accept_3_3 32 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 229 (Polychromatic418967fa.accept_17_14_7_8_1_7544 31 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 229 (accept_3_3 29 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 229 (Polychromatic418967fa.accept_18_10_1_13_1_2192 28 109 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 229 (accept_3_3 26 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 229 (accept_3_3 23 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 229 (accept_3_3 20 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 229 (Polychromatic418967fa.accept_16_2_13_5_1_2257 18 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 229 (accept_3_3 17 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 109 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 229 (accept_3_3 14 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 229 (accept_3_3 11 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 229 (Polychromatic418967fa.accept_13_10_5_8_1_2555 10 109 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 229 (accept_3_3 8 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 229 (accept_3_3 5 109 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 229 (Polychromatic418967fa.accept_17_4_7_8_1_7491 4 109 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 229 (accept_3_3 2 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 109 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 229 (allA_succ_of_accept 107 108 229 (accept_3_3 107 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 108 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 106 108 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 105 108
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 229 (accept_3_3 104 108
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 108 229
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 103 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 108 229 (Polychromatic418967fa.accept_13_11_4_8_1_1098 102 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 229 (accept_3_3 101 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 100 108
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 99 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 108 229 (accept_3_3 98 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 108 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 97 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 108 229 (Polychromatic418967fa.accept_14_12_10_5_1_2712 96 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 108 229 (accept_3_3 95 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 94 108
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 93 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 108 229 (accept_3_3 92 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 108 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 91 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 108 229 (Polychromatic418967fa.accept_13_12_4_8_1_1120 90 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 108 229 (accept_3_3 89 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 229 (Polychromatic418967fa.accept_13_10_4_8_1_2570 88 108
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 229
  (Polychromatic418967fa.accept_10_7_8_9_1_785 87 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 108 229 (accept_3_3 86 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 108 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 108 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 84 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 229 (accept_3_3 83 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 229 (Polychromatic418967fa.accept_14_12_10_5_1_2712 82 108
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 229
  (Polychromatic418967fa.accept_8_1_4_5_1_48 81 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 108 229 (accept_3_3 80 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 108 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 79 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 108 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 229 (accept_3_3 77 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 229 (Polychromatic418967fa.accept_13_11_4_8_1_1098 76 108 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 229
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 75 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 108 229 (accept_3_3 74 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 108 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 108 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 229 (accept_3_3 71 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 229 (Polychromatic418967fa.accept_22_4_20_9_1_12110 70 108 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 229
  (Polychromatic418967fa.accept_19_12_13_1_1_2779 69 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 108 229 (accept_3_3 68 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 108 229 (Polychromatic418967fa.accept_10_7_8_9_1_785 67 108 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 108 229 (Polychromatic418967fa.accept_17_15_6_8_1_6343 66 108
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 108 229 (accept_3_3 65 108
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 64 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 108 229 (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 108 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 229 (accept_3_3 62 108 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 108 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 61 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 108 229
  (Polychromatic418967fa.accept_17_9_6_8_1_6315 60 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 108 229 (accept_3_3 59 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 108 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 108 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 229 (accept_3_3 56 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 229 (Polychromatic418967fa.accept_16_7_12_5_1_734 55 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 229
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 108 229 (accept_3_3 53 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 108 229 (Polychromatic418967fa.accept_15_7_3_4_1_574 52 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 108 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 229 (accept_3_3 50 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 229
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 48 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 108 229 (accept_3_3 47 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 108 229 (Polychromatic418967fa.accept_15_1_3_4_1_1217 46 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 108 229 (Polychromatic418967fa.accept_19_7_13_1_1_6804 45 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 229 (accept_3_3 44 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 108 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 229
  (Polychromatic418967fa.accept_16_10_12_5_1_2254 42 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 108 229 (accept_3_3 41 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 108 229 (Polychromatic418967fa.accept_14_12_10_5_1_2712 40 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 229 (Polychromatic418967fa.accept_16_7_12_5_1_734
  39 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 229 (accept_3_3 38
  108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 108 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 108 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 229 (accept_3_3 35 108 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 108 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 229
  (Polychromatic418967fa.accept_8_1_4_5_1_48 33 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 229 (accept_3_3 32 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 108 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 108 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 229 (accept_3_3 29 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 229 (Polychromatic418967fa.accept_22_6_20_9_1_9031 28 108 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 229
  (Polychromatic418967fa.accept_10_7_8_9_1_785 27 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 108 229 (accept_3_3 26 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 108 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 108 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 229 (accept_3_3 23 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 108 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 229
  (Polychromatic418967fa.accept_10_1_8_9_1_787 21 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 229 (accept_3_3 20 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 108 229 (Polychromatic418967fa.accept_20_19_8_9_1_4963 19 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 108 229 (Polychromatic418967fa.accept_19_18_13_1_1_9735 18 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 229 (accept_3_3 17 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 108 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 108 229 (accept_3_3 14 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 108 229 (Polychromatic418967fa.accept_42_13_24_19_1_13693 13 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 229 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 108 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 229 (accept_3_3 11 108 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 229
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 10 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 108 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 229 (accept_3_3 8 108 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 108 229 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 108 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 229
  (Polychromatic418967fa.accept_21_6_3_19_1_10785 6 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 108 229 (accept_3_3 5 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  108 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 108 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 108 229 (Polychromatic418967fa.accept_22_3_20_9_1_13692 3 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 229 (accept_3_3 2 108 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 108 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 229 (allA_of_3_1 107 107 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 229
  (allA_succ_of_accept 105 106 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 106 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 229 (accept_3_3 104 106 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 102 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 106 229 (accept_3_3 101 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 106 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 100 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 229 (accept_3_3 98 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 97 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 96 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 229 (accept_3_3 95 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 94 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 229 (accept_3_3 92 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 90 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 106 229 (accept_3_3 89 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 106 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 88 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 229 (accept_3_3 86 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 229 (Polychromatic418967fa.accept_10_5_6_9_1_2235 85 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 229 (accept_3_3 83 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 229 (accept_3_3 80 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 229 (accept_3_3 77 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 229 (accept_3_3 74 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 229
  (Polychromatic418967fa.accept_13_7_2_8_1_1746 72 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 229 (accept_3_3 71 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 229 (Polychromatic418967fa.accept_20_10_6_9_1_4989 70 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 229 (accept_3_3 68 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 229 (accept_3_3 65 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 229 (accept_3_3 62 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 229 (Polychromatic418967fa.accept_16_13_10_5_1_2278 61 106 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 229 (accept_3_3 59 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 58 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 229 (accept_3_3 56 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 229
  (Polychromatic418967fa.accept_20_14_6_9_1_9460 54 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 229 (accept_3_3 53 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 229 (accept_3_3 50 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 229 (accept_3_3 47 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 229 (accept_3_3 44 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 229 (accept_3_3 41 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 229 (accept_3_3 38 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 229
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 229 (accept_3_3 35 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 229 (accept_3_3 32 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 229 (accept_3_3 29 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 229 (accept_3_3 26 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 229 (accept_3_3 23 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 229 (Polychromatic418967fa.accept_19_3_11_1_1_8319 22 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 229 (accept_3_3 20 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 229 (accept_3_3 17 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 229 (accept_3_3 14 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 229 (accept_3_3 11 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 229 (accept_3_3 8 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 229 (accept_3_3 5 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 106 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 229 (accept_3_3 2 106 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 106 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 229 (allA_succ_of_accept 104 105 229 (accept_3_3 104 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 229 (Polychromatic418967fa.accept_13_12_1_8_1_1779 103 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 229 (Polychromatic418967fa.accept_9_3_6_4_1_210
  102 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 229 (accept_3_3
  101 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 229
  (Polychromatic418967fa.accept_6_4_3_1_1_57 100 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 99 105 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 229 (accept_3_3 98 105 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 105 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 97 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 229 (Polychromatic418967fa.accept_10_6_5_9_1_1233
  96 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 229 (accept_3_3 95
  105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 229
  (Polychromatic418967fa.accept_6_4_3_1_1_57 94 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 105 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 229 (accept_3_3 92 105 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 105 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 229
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 90 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 105 229 (accept_3_3 89 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 105 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 87 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 229 (accept_3_3 86 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 229 (Polychromatic418967fa.accept_13_7_1_8_1_1778 85 105
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 84 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 105 229 (accept_3_3 83 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 105 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 229 (accept_3_3 80 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 105 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 229
  (Polychromatic418967fa.accept_16_14_9_5_1_4388 78 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 105 229 (accept_3_3 77 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 105 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 229 (accept_3_3 74 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 229
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 72 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 105 229 (accept_3_3 71 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 105 229 (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 229 (accept_3_3 68 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 229 (Polychromatic418967fa.accept_20_7_5_9_1_10833 67 105
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 229 (accept_3_3 65 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 105 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 63 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 229 (accept_3_3 62 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 105 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 105 229 (accept_3_3 59 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 229 (accept_3_3 56 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 229
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 229 (accept_3_3 53 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 229 (accept_3_3 50 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 229 (Polychromatic418967fa.accept_16_1_9_5_1_5443 49 105
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 229 (accept_3_3 47 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 229 (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 229 (accept_3_3 44 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 105 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 229
  (Polychromatic418967fa.accept_19_4_10_1_1_2776 42 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 229 (accept_3_3 41 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 229 (accept_3_3 38 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 229 (accept_3_3 35 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 229 (Polychromatic418967fa.accept_13_7_1_8_1_1778 33 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 229 (accept_3_3 32 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 105
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 229 (accept_3_3 29 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 229 (accept_3_3 26 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 105 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 229
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 229 (accept_3_3 23 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 229 (accept_3_3 20 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 229
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 229 (accept_3_3 17 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 229 (accept_3_3 14 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 229 (Polychromatic418967fa.accept_16_13_9_5_1_3302 13 105
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 229 (accept_3_3 11 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 229 (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 229 (accept_3_3 8 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 229
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 229 (accept_3_3 5 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 229 (accept_3_3 2 105 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 105 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 229 (allA_of_3_1 104 104 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 229
  (allA_succ_of_accept 102 103 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 103 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 229 (accept_3_3 101 103 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 229 (Polychromatic418967fa.accept_13_9_12_8_1_570 100 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 229
  (Polychromatic418967fa.accept_15_9_13_4_1_1209 99 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 229 (accept_3_3 98 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 229 (Polychromatic418967fa.accept_19_2_8_1_1_4065 97 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 96 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 229 (accept_3_3 95 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 103 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 229
  (Polychromatic418967fa.accept_22_5_15_9_1_10649 93 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 103 229 (accept_3_3 92 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 103 229 (Polychromatic418967fa.accept_16_11_7_5_1_4364 91 103 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 103 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 103 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 229 (accept_3_3 89 103 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 229
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 88 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 103 229 (Polychromatic418967fa.accept_13_9_12_8_1_570 87 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 103 229 (accept_3_3 86 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 103 229 (Polychromatic418967fa.accept_13_7_12_8_1_199 85 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 103 229
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 84 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 103 229 (accept_3_3 83 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 103 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 103 229 (Polychromatic418967fa.accept_15_6_13_4_1_2040 81 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 103 229 (accept_3_3 80 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 103 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 79 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 103 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 103 229 (accept_3_3 77 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 103 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 76 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 103 229 (Polychromatic418967fa.accept_13_10_12_8_1_2550 75 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 103 229 (accept_3_3 74 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 103 229 (Polychromatic418967fa.accept_19_16_8_1_1_8259 73 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 229
  (Polychromatic418967fa.accept_13_7_12_8_1_199 72 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 103 229 (accept_3_3 71 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 103 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 103 229 (Polychromatic418967fa.accept_13_4_12_8_1_197 69 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 229 (accept_3_3 68 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 103 229 (Polychromatic418967fa.accept_22_1_15_9_1_13691 67 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 103 229 (accept_3_3 65 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 103 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 64 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 103 229 (Polychromatic418967fa.accept_24_15_7_13_1_13690 63 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 229 (accept_3_3 62 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 229 (Polychromatic418967fa.accept_13_9_12_8_1_570 61 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 229
  (Polychromatic418967fa.accept_16_12_7_5_1_1412 60 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 103 229 (accept_3_3 59 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 57 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 229 (accept_3_3 56 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 229 (Polychromatic418967fa.accept_15_10_13_4_1_1210 55 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 229 (accept_3_3 53 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 229 (Polychromatic418967fa.accept_20_12_3_9_1_10866 52 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 229 (Polychromatic418967fa.accept_15_6_13_4_1_2040 51 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 229 (accept_3_3 50 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 229 (Polychromatic418967fa.accept_13_10_12_8_1_2550 49 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 229
  (Polychromatic418967fa.accept_13_9_12_8_1_570 48 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 229 (accept_3_3 47 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 229 (Polychromatic418967fa.accept_17_11_1_8_1_7502 45 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 229 (accept_3_3 44 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 229 (Polychromatic418967fa.accept_13_4_12_8_1_197 43 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 229 (accept_3_3 41 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 229 (Polychromatic418967fa.accept_13_1_12_8_1_1818 40 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 229 (Polychromatic418967fa.accept_15_9_13_4_1_1209 39 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 229 (accept_3_3 38 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 229 (Polychromatic418967fa.accept_19_18_8_1_1_11071 37 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 229
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 229 (accept_3_3 35 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 229 (Polychromatic418967fa.accept_13_7_12_8_1_199 33 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 229 (accept_3_3 32 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 229 (Polychromatic418967fa.accept_13_5_12_8_1_198 31 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 229 (accept_3_3 29 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 229 (Polychromatic418967fa.accept_16_12_7_5_1_1412 28 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 229 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 229 (accept_3_3 26 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 229 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 229
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 229 (accept_3_3 23 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 229 (Polychromatic418967fa.accept_15_6_13_4_1_2040 21 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 229 (accept_3_3 20 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 229 (Polychromatic418967fa.accept_20_19_3_9_1_7965 19 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 229 (accept_3_3 17 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 229 (Polychromatic418967fa.accept_19_15_8_1_1_6794 15 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 229 (accept_3_3 14 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 229
  (Polychromatic418967fa.accept_16_12_7_5_1_1412 12 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 229 (accept_3_3 11 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 229 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 103 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 229 (accept_3_3 8 103 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 229 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 229 (accept_3_3 5 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 103 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 229 (Polychromatic418967fa.accept_22_3_15_9_1_10617 3 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 229 (accept_3_3 2 103 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 229 (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 103
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 229 (allA_succ_of_accept 101 102 229 (accept_3_3 101 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 102 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 100 102 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 102 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 229 (accept_3_3 98 102 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 229 (Polychromatic418967fa.accept_7_6_4_5_1_314
  97 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 96 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 229 (accept_3_3 95 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 102 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 94 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 93 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 229 (accept_3_3 92 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 90 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 102 229 (accept_3_3 89 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 102 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 229 (accept_3_3 86 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 229
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 84 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 102 229 (accept_3_3 83 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 102 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 102 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 81 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 229 (accept_3_3 80 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 102 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 78 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 102 229 (accept_3_3 77 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 102 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 229 (accept_3_3 74 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 72 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 102 229 (accept_3_3 71 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 102 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 102 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 229 (accept_3_3 68 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 229
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 66 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 102 229 (accept_3_3 65 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 102 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 229 (accept_3_3 62 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 229 (accept_3_3 59 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 102 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 229 (accept_3_3 56 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 229
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 54 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 102 229 (accept_3_3 53 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 102 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 229 (accept_3_3 50 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 229 (Polychromatic418967fa.accept_13_10_11_8_1_1770 49 102 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 102 229 (accept_3_3 47 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 102 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 102 229 (Polychromatic418967fa.accept_13_6_11_8_1_1111 45 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 229 (accept_3_3 44 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 102 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 229 (accept_3_3 41 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 229 (Polychromatic418967fa.accept_13_1_11_8_1_2562 40 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 229 (accept_3_3 38 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 102 229 (accept_3_3 35 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 102 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 102 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 229 (accept_3_3 32 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 102 229 (accept_3_3 29 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 102 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 229 (accept_3_3 26 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 229 (accept_3_3 23 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 229 (accept_3_3 20 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 229
  (Polychromatic418967fa.accept_19_18_7_1_1_2770 18 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 229 (accept_3_3 17 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 229 (accept_3_3 14 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 229
  (Polychromatic418967fa.accept_19_12_7_1_1_5400 12 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 229 (accept_3_3 11 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 229 (accept_3_3 8 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 229 (accept_3_3 5 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 229 (Polychromatic418967fa.accept_13_4_11_8_1_1768 4 102 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 229 (accept_3_3 2 102 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 102 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 229 (allA_of_3_1 101 101 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 229 (allA_succ_of_accept 99
  100 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 100 229 (accept_3_3 98 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 100 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 97 100 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 100 229 (accept_3_3 95 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 100 229 (Polychromatic418967fa.accept_7_3_2_5_1_147
  94 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 100 229 (accept_3_3 92 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 100 229 (Polychromatic418967fa.accept_14_7_2_5_1_4528 91 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 100 229 (Polychromatic418967fa.accept_13_12_9_8_1_2595 90 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 100 229 (accept_3_3 89 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 100 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 100 229 (accept_3_3 86 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 100 229 (Polychromatic418967fa.accept_13_7_9_8_1_188 85 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 100 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 100 229 (accept_3_3 83 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 100 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 82 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 100 229 (accept_3_3 80 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 100 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 100 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 100 229 (accept_3_3 77 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 100 229 (Polychromatic418967fa.accept_11_10_1_9_1_2060 76 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 100 229 (accept_3_3 74 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 100 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 100 229 (Polychromatic418967fa.accept_13_7_9_8_1_188 72 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 100 229 (accept_3_3 71 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 100 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 100 229 (accept_3_3 68 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 100 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 100 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 100 229 (accept_3_3 65 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 100 229 (Polychromatic418967fa.accept_13_12_9_8_1_2595 64 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 100 229 (accept_3_3 62 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 100 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 100 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 100 229 (accept_3_3 59 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 100 229 (accept_3_3 56 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 100 229 (Polychromatic418967fa.accept_13_3_9_8_1_4202 55 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 100 229 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 100 229 (accept_3_3 53 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 100 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 100 229 (accept_3_3 50 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 100 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 100 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 229 (accept_3_3 47 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 100 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 100 229 (accept_3_3 44 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 100 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 100 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 100 229 (accept_3_3 41 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 100 229 (Polychromatic418967fa.accept_13_1_9_8_1_1734 40 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 100 229 (accept_3_3 38 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 100 229 (Polychromatic418967fa.accept_13_11_9_8_1_1125 37 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 100 229 (Polychromatic418967fa.accept_15_6_10_4_1_150 36 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 229 (accept_3_3 35 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 100 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 100 229 (accept_3_3 32 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 100 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 100 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 229 (accept_3_3 29 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 229 (accept_3_3 26 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 100 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 100 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 229 (accept_3_3 23 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 100 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 229 (accept_3_3 20 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 229 (Polychromatic418967fa.accept_18_1_10_13_1_500 19 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 229 (accept_3_3 17 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 229 (accept_3_3 14 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 229 (accept_3_3 11 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 229 (accept_3_3 8 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 229 (accept_3_3 5 100 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 100 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 229 (accept_3_3 2 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 100 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  229 (allA_succ_of_accept 98 99 229 (accept_3_3 98 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 97 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 229 (Polychromatic418967fa.accept_15_6_9_4_1_1227 96 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 229 (accept_3_3 95 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 93 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 229 (accept_3_3 92 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 229 (Polychromatic418967fa.accept_17_6_14_8_1_3858 91 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 229 (accept_3_3 89 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 87 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 229 (accept_3_3 86 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 229 (Polychromatic418967fa.accept_15_10_9_4_1_2924 85 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 229 (Polychromatic418967fa.accept_17_16_14_8_1_7608 84 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 229 (accept_3_3 83 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 81 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 229 (accept_3_3 80 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 229 (Polychromatic418967fa.accept_17_11_14_8_1_2729 79 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 229 (accept_3_3 77 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 229
  (Polychromatic418967fa.accept_17_7_14_8_1_5069 75 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 229 (accept_3_3 74 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 229 (Polychromatic418967fa.accept_15_12_9_4_1_3898 72 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 229 (accept_3_3 71 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 229 (accept_3_3 68 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 229 (accept_3_3 65 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 229
  (Polychromatic418967fa.accept_20_3_19_9_1_4976 63 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 229 (accept_3_3 62 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 229 (Polychromatic418967fa.accept_22_17_11_9_1_10636 61 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 229 (accept_3_3 59 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 229 (accept_3_3 56 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 229 (accept_3_3 53 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 229
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 51 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 229 (accept_3_3 50 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 229 (Polychromatic418967fa.accept_21_7_15_19_1_10726 49 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 229 (accept_3_3 47 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 229 (accept_3_3 44 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 229 (Polychromatic418967fa.accept_15_13_9_4_1_3892 43 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 229 (accept_3_3 41 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 229 (accept_3_3 38 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 229 (Polychromatic418967fa.accept_25_12_24_4_1_13689 37 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 229 (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 229 (accept_3_3 35 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 229 (accept_3_3 32 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 229 (accept_3_3 29 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 229 (accept_3_3 26 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 229 (accept_3_3 23 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 229 (accept_3_3 20 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 229 (Polychromatic418967fa.accept_22_19_11_9_1_9028 19 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 229 (accept_3_3 17 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 229
  (Polychromatic418967fa.accept_19_15_4_1_1_4060 15 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 229 (accept_3_3 14 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 229 (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 229 (accept_3_3 11 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 229 (accept_3_3 8 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  229 (Polychromatic418967fa.accept_17_7_14_8_1_5069 7 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 229 (accept_3_3 5 99 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 229 (accept_3_3 2 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  229 (Polychromatic418967fa.accept_21_1_15_19_1_4491 1 99 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  229 (allA_of_3_1 98 98 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 229 (allA_succ_of_accept 96 97 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 96 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 229 (accept_3_3 95 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 229 (Polychromatic418967fa.accept_18_4_7_13_1_3303 94 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 93 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 229 (accept_3_3 92 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 229
  (Polychromatic418967fa.accept_14_6_13_5_1_534 90 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 229 (accept_3_3 89 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 87 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 229 (accept_3_3 86 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 85 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 84 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 229 (accept_3_3 83 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 229 (accept_3_3 80 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 229 (Polychromatic418967fa.accept_13_1_6_8_1_208 79 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 78 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 229 (accept_3_3 77 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 76 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 229 (accept_3_3 74 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 229
  (Polychromatic418967fa.accept_10_2_7_9_1_783 72 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 229 (accept_3_3 71 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 229 (Polychromatic418967fa.accept_15_10_7_4_1_1222 70 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 229 (accept_3_3 68 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 229 (accept_3_3 65 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 229 (Polychromatic418967fa.accept_13_11_6_8_1_1121 63 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 229 (accept_3_3 62 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 229 (Polychromatic418967fa.accept_16_13_1_5_1_5469 61 97
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 229 (accept_3_3 59 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 229 (Polychromatic418967fa.accept_10_8_7_9_1_425 58 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 229 (accept_3_3 56 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 229
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 54 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 229 (accept_3_3 53 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 229 (accept_3_3 50 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 229 (Polychromatic418967fa.accept_21_7_13_19_1_4477 49 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 229 (accept_3_3 47 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 229 (Polychromatic418967fa.accept_16_13_1_5_1_5469 45 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 229 (accept_3_3 44 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 97 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 229 (accept_3_3 41 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 229 (Polychromatic418967fa.accept_13_1_6_8_1_208 40 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 229 (accept_3_3 38 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 229 (accept_3_3 35 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 229 (Polychromatic418967fa.accept_14_6_13_5_1_534 34 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 229 (accept_3_3 32 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 229 (Polychromatic418967fa.accept_16_15_1_5_1_2265 31 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 229 (accept_3_3 29 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 229 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 229 (accept_3_3 26 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 229 (accept_3_3 23 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 229 (accept_3_3 20 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 229 (accept_3_3 17 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 229 (Polychromatic418967fa.accept_21_16_13_19_1_6035 16 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 229 (accept_3_3 14 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 229 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 229 (accept_3_3 11 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 229 (Polychromatic418967fa.accept_16_9_1_5_1_2282 9 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 229 (accept_3_3 8 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 229 (Polychromatic418967fa.accept_19_7_2_1_1_4076 7 97 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 229 (accept_3_3 5 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 97 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 97 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 229 (accept_3_3 2 97 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 97 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 229
  (allA_succ_of_accept 95 96 229 (accept_3_3 95 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  96 229 (Polychromatic418967fa.accept_13_3_5_8_1_1099 94 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 96 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 96 229 (accept_3_3 92 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 229
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 90 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 96 229 (accept_3_3 89 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  96 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 96 229 (Polychromatic418967fa.accept_11_10_8_9_1_492 87 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 229 (accept_3_3 86 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 229 (Polychromatic418967fa.accept_10_5_6_9_1_2235 85 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 229 (accept_3_3 83 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  96 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 229 (Polychromatic418967fa.accept_13_3_5_8_1_1099 81 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 229 (accept_3_3 80 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 229
  (Polychromatic418967fa.accept_21_15_12_19_1_10724 78 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 96 229 (accept_3_3 77 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 229 (Polychromatic418967fa.accept_11_10_8_9_1_492 76 96 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 96 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 96 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 229 (accept_3_3 74 96 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 73
  96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 229
  (Polychromatic418967fa.accept_21_9_12_19_1_12172 72 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 96 229 (accept_3_3 71 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 96 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 96 229 (Polychromatic418967fa.accept_15_9_6_4_1_1220 69 96 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 229 (accept_3_3 68 96 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 229 (Polychromatic418967fa.accept_20_7_16_9_1_4970
  67 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 229 (accept_3_3 65 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 229 (accept_3_3 62 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 229
  (Polychromatic418967fa.accept_17_9_11_8_1_5077 60 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 229 (accept_3_3 59 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 229 (Polychromatic418967fa.accept_15_13_6_4_1_1221 58 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 229 (accept_3_3 56 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 229
  (Polychromatic418967fa.accept_11_10_8_9_1_492 54 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 229 (accept_3_3 53 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 229 (Polychromatic418967fa.accept_13_12_5_8_1_1101 51 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 229 (accept_3_3 50 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 229 (Polychromatic418967fa.accept_13_10_5_8_1_2555 49 96
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 229 (accept_3_3 47 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 229 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 229 (accept_3_3 44 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 229
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 42 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 229 (accept_3_3 41 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 229 (Polychromatic418967fa.accept_13_1_5_8_1_207 40 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 229 (accept_3_3 38 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 229
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 229 (accept_3_3 35 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 229 (accept_3_3 32 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 229 (Polychromatic418967fa.accept_14_3_12_5_1_153 31 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 229 (accept_3_3 29 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 229 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 229 (accept_3_3 26 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 229
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 229 (accept_3_3 23 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 229 (Polychromatic418967fa.accept_21_1_12_19_1_7721 22 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 229 (accept_3_3 20 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 229
  (Polychromatic418967fa.accept_17_1_11_8_1_2725 18 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 229 (accept_3_3 17 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 229 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 229 (accept_3_3 14 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 229 (accept_3_3 11 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 229 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 229 (accept_3_3 8 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 229
  (Polychromatic418967fa.accept_21_6_12_19_1_6032 6 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 229 (accept_3_3 5 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  229 (Polychromatic418967fa.accept_21_4_12_19_1_4513 4 96 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 96 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 229 (accept_3_3 2 96 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 96 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 229
  (allA_of_3_1 95 95 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 229 (allA_succ_of_accept 93 94 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 94 229 (accept_3_3 92 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  94 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 94 229 (Polychromatic418967fa.accept_16_10_14_5_1_5496 90 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 229 (accept_3_3 89 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 88 94 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 94 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 94 229 (accept_3_3 86 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  94 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 94 229 (Polychromatic418967fa.accept_17_16_9_8_1_5063 84 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 229 (accept_3_3 83 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 229 (Polychromatic418967fa.accept_14_12_10_5_1_2712 82 94
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 229 (accept_3_3 80 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 229 (accept_3_3 77 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 76 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 229 (accept_3_3 74 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 73 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 229 (accept_3_3 71 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 229 (Polychromatic418967fa.accept_13_5_3_8_1_1117 70 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 229 (accept_3_3 68 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 229 (Polychromatic418967fa.accept_20_6_14_9_1_3489 66 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 229 (accept_3_3 65 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 94 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 229 (accept_3_3 62 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 229 (Polychromatic418967fa.accept_13_9_3_8_1_573 61 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 229 (Polychromatic418967fa.accept_22_16_6_9_1_12085 60 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 229 (accept_3_3 59 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 94 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 229 (accept_3_3 56 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 229 (Polychromatic418967fa.accept_14_12_10_5_1_2712 54 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 229 (accept_3_3 53 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 94 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 229 (accept_3_3 50 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 229 (Polychromatic418967fa.accept_19_11_18_1_1_4048 49 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 229 (accept_3_3 47 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 229 (Polychromatic418967fa.accept_13_7_3_8_1_1750 46 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 229 (accept_3_3 44 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 229 (Polychromatic418967fa.accept_16_10_14_5_1_5496 42 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 229 (accept_3_3 41 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 94 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 229 (accept_3_3 38 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 229 (accept_3_3 35 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 229 (Polychromatic418967fa.accept_23_11_2_22_1_7053 34 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 229 (accept_3_3 32 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 229 (accept_3_3 29 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 229 (accept_3_3 26 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 229 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 229 (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 229 (accept_3_3 23 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 94 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 229 (accept_3_3 20 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 229 (accept_3_3 17 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 229 (accept_3_3 14 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 229 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 229 (accept_3_3 11 94 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 229 (Polychromatic418967fa.accept_16_10_14_5_1_5496 10 94
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 229 (accept_3_3 8 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 229 (Polychromatic418967fa.accept_17_6_9_8_1_6316 6 94 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 229 (accept_3_3 5 94 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 94 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 229 (accept_3_3 2 94 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 94
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 229
  (allA_succ_of_accept 92 93 229 (accept_3_3 92 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 229 (Polychromatic418967fa.accept_16_10_13_5_1_3292 90 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 229 (accept_3_3 89 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 93 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 87 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 229 (accept_3_3 86 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 229 (Polychromatic418967fa.accept_13_7_2_8_1_1746 85 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 84 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 229 (accept_3_3 83 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 81 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 229 (accept_3_3 80 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 229 (accept_3_3 77 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 229 (accept_3_3 74 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 229 (Polychromatic418967fa.accept_13_7_2_8_1_1746 72 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 229 (accept_3_3 71 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 229 (accept_3_3 68 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 229 (accept_3_3 65 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 229 (accept_3_3 62 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 229 (accept_3_3 59 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 229
  (Polychromatic418967fa.accept_16_9_13_5_1_2238 57 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 229 (accept_3_3 56 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 229 (accept_3_3 53 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 229 (accept_3_3 50 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 229 (Polychromatic418967fa.accept_13_10_2_8_1_2603 49 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 229 (Polychromatic418967fa.accept_18_12_3_13_1_4494 48 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 229 (accept_3_3 47 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 93 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 229 (accept_3_3 44 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 229 (accept_3_3 41 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 229 (accept_3_3 38 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 229 (accept_3_3 35 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 229 (accept_3_3 32 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 229 (Polychromatic418967fa.accept_18_12_3_13_1_4494 30 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 229 (accept_3_3 29 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 229 (accept_3_3 26 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 229 (accept_3_3 23 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 229
  (Polychromatic418967fa.accept_14_7_9_5_1_529 21 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 229 (accept_3_3 20 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 229 (accept_3_3 17 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 229 (accept_3_3 14 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 229 (Polychromatic418967fa.accept_26_13_15_21_1_13688 13 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 229 (Polychromatic418967fa.accept_18_12_3_13_1_4494 12 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 229 (accept_3_3 11 93 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 93 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 229
  (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 229 (accept_3_3 8 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 93 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 229 (accept_3_3 5 93 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  93 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 229 (accept_3_3 2 93 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 93
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 229
  (allA_of_3_1 92 92 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 229 (allA_succ_of_accept 90 91 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 229 (accept_3_3 89 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 87 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 229 (accept_3_3 86 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 85 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 91 229 (accept_3_3 83 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 229 (Polychromatic418967fa.accept_19_5_15_1_1_4041 81 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 229 (accept_3_3 80 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 91 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 91 229 (accept_3_3 77 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 229 (Polychromatic418967fa.accept_21_13_7_19_1_4505 76 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 229 (accept_3_3 74 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 229 (Polychromatic418967fa.accept_16_9_11_5_1_2279 73 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 229
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 229 (accept_3_3 71 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 229 (accept_3_3 68 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 229 (Polychromatic418967fa.accept_21_4_7_19_1_13687 67 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 229 (accept_3_3 65 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 229 (Polychromatic418967fa.accept_18_10_1_13_1_2192 64 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 229 (Polychromatic418967fa.accept_15_3_1_4_1_1246 63 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 229 (accept_3_3 62 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 229 (accept_3_3 59 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 229 (accept_3_3 56 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 55 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 229 (accept_3_3 53 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 229 (accept_3_3 50 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 229 (Polychromatic418967fa.accept_17_15_6_8_1_6343 49 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 229 (accept_3_3 47 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 229 (accept_3_3 44 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 229 (accept_3_3 41 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 229 (Polychromatic418967fa.accept_14_12_7_5_1_1107 40 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 229 (accept_3_3 38 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 229 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 229
  (Polychromatic418967fa.accept_19_17_15_1_1_8300 36 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 229 (accept_3_3 35 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 229 (accept_3_3 32 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 229 (Polychromatic418967fa.accept_17_14_6_8_1_7688 31 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 229 (accept_3_3 29 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 28 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 229 (Polychromatic418967fa.accept_15_12_1_4_1_2899 27 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 229 (accept_3_3 26 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 91 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 229 (accept_3_3 23 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 229 (accept_3_3 20 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 229 (Polychromatic418967fa.accept_26_19_13_21_1_13686 19 91 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 229 (accept_3_3 17 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 229 (accept_3_3 14 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 229 (Polychromatic418967fa.accept_21_13_7_19_1_4505 13 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 229 (accept_3_3 11 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 229 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 229 (accept_3_3 8 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 229 (accept_3_3 5 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  229 (Polychromatic418967fa.accept_19_4_15_1_1_2819 4 91 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 229 (accept_3_3 2 91 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 229 (Polychromatic418967fa.accept_21_1_7_19_1_9193 1 91 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 229
  (allA_succ_of_accept 89 90 229 (accept_3_3 89 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  90 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 229 (accept_3_3 86 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 85 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 229
  (Polychromatic418967fa.accept_11_7_2_9_1_480 84 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 229 (accept_3_3 83 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  90 229 (Polychromatic418967fa.accept_13_4_12_8_1_197 82 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 90 229 (accept_3_3 80 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 78 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 90 229 (accept_3_3 77 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  90 229 (Polychromatic418967fa.accept_16_12_10_5_1_5457 76 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 229 (accept_3_3 74 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 73 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 229
  (Polychromatic418967fa.accept_13_7_12_8_1_199 72 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 90 229 (accept_3_3 71 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  90 229 (Polychromatic418967fa.accept_11_4_2_9_1_496 70 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 90 229 (Polychromatic418967fa.accept_13_4_12_8_1_197 69 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 229 (accept_3_3 68 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 229
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 66 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 90 229 (accept_3_3 65 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  90 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 229 (accept_3_3 62 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 229 (Polychromatic418967fa.accept_13_9_12_8_1_570 61 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 90 229 (accept_3_3 59 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  90 229 (Polychromatic418967fa.accept_25_8_15_4_1_13685 58 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 90 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 229 (accept_3_3 56 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 229
  (Polychromatic418967fa.accept_17_3_5_8_1_1687 54 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 90 229 (accept_3_3 53 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  90 229 (Polychromatic418967fa.accept_23_6_21_22_1_13684 52 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 229 (accept_3_3 50 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 229 (Polychromatic418967fa.accept_13_10_12_8_1_2550 49 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 229
  (Polychromatic418967fa.accept_11_4_2_9_1_496 48 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 90 229 (accept_3_3 47 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  90 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 90 229 (Polychromatic418967fa.accept_16_13_10_5_1_2278 45 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 229 (accept_3_3 44 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 229
  (Polychromatic418967fa.accept_27_15_9_13_1_13683 42 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 90 229 (accept_3_3 41 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 90 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 229 (accept_3_3 38 90 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 229 (Polychromatic418967fa.accept_11_4_2_9_1_496
  37 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 229 (accept_3_3 35 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  90 229 (Polychromatic418967fa.accept_19_15_14_1_1_8297 34 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 229 (Polychromatic418967fa.accept_13_7_12_8_1_199 33 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 229 (accept_3_3 32 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 229
  (Polychromatic418967fa.accept_13_4_12_8_1_197 30 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 229 (accept_3_3 29 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 229 (Polychromatic418967fa.accept_16_12_10_5_1_5457 28 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 229 (accept_3_3 26 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 229
  (Polychromatic418967fa.accept_21_3_6_19_1_3125 24 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 229 (accept_3_3 23 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  90 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 229 (Polychromatic418967fa.accept_19_2_14_1_1_11076 21 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 229 (accept_3_3 20 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 90 229 (accept_3_3 17 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  90 229 (Polychromatic418967fa.accept_20_16_10_9_1_9431 16 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 229 (accept_3_3 14 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 229 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 229
  (Polychromatic418967fa.accept_16_12_10_5_1_5457 12 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 229 (accept_3_3 11 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 229 (Polychromatic418967fa.accept_13_10_12_8_1_2550 10 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 229 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 229 (accept_3_3 8 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 229
  (Polychromatic418967fa.accept_19_6_14_1_1_2752 6 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 229 (accept_3_3 5 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 90 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 90 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 229 (accept_3_3 2 90 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 90 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 90 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 229
  (allA_of_3_1 89 89 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 229 (allA_succ_of_accept 87 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 88 229 (accept_3_3 86 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  88 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 88 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 229 (accept_3_3 83 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 88 229 (accept_3_3 80 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  88 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 88 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 229 (accept_3_3 77 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 229 (accept_3_3 74 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 229 (accept_3_3 71 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 229 (accept_3_3 68 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 229 (Polychromatic418967fa.accept_10_7_8_9_1_785 67 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 88 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 229 (accept_3_3 65 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 88 229 (accept_3_3 62 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  88 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 61 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 88 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 229 (accept_3_3 59 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 229 (accept_3_3 56 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 229 (accept_3_3 53 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 229 (Polychromatic418967fa.accept_16_4_8_5_1_3317 52 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 229 (accept_3_3 50 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 229 (Polychromatic418967fa.accept_19_11_12_1_1_11049 49 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 229 (accept_3_3 47 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 229 (accept_3_3 44 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 229 (accept_3_3 41 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 229 (Polychromatic418967fa.accept_15_10_13_4_1_1210 40 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 229 (accept_3_3 38 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 229 (accept_3_3 35 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 229 (accept_3_3 32 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 229 (accept_3_3 29 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 229 (accept_3_3 26 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 229 (Polychromatic418967fa.accept_13_12_10_8_1_3343 25 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 229 (accept_3_3 23 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 229 (accept_3_3 20 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 229 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 229 (accept_3_3 17 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 88 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 229 (accept_3_3 14 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 229 (accept_3_3 11 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 88 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 229 (accept_3_3 8 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  229 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 88 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 88 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 88 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 229 (accept_3_3 5 88 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 88 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 88 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 229 (accept_3_3 2 88 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 88
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 229
  (allA_succ_of_accept 86 87 229 (accept_3_3 86 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  87 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 229 (accept_3_3 83 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 81 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 229 (accept_3_3 80 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 79 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 229 (accept_3_3 77 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 229 (accept_3_3 74 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 229 (accept_3_3 71 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 69 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 229 (accept_3_3 68 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 229 (Polychromatic418967fa.accept_11_1_10_9_1_871 67 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 229 (accept_3_3 65 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 229
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 229 (accept_3_3 62 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 229 (Polychromatic418967fa.accept_16_12_7_5_1_1412 60 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 229 (accept_3_3 59 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 229 (accept_3_3 56 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 229 (accept_3_3 53 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 229 (accept_3_3 50 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 229 (Polychromatic418967fa.accept_23_3_18_22_1_13682 49 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 229 (accept_3_3 47 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 229
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 229 (accept_3_3 44 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 229 (accept_3_3 41 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 229 (accept_3_3 38 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 229 (accept_3_3 35 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 229 (accept_3_3 32 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 229 (Polychromatic418967fa.accept_15_1_12_4_1_2022 31 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 229 (accept_3_3 29 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 229
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 229 (accept_3_3 26 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 229 (Polychromatic418967fa.accept_13_11_9_8_1_1125 24 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 229 (accept_3_3 23 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 229 (accept_3_3 20 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 229 (accept_3_3 17 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 229 (accept_3_3 14 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 229 (Polychromatic418967fa.accept_22_13_21_9_1_4104 13 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 229 (accept_3_3 11 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 229 (accept_3_3 8 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 229 (accept_3_3 5 87 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  87 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 229 (accept_3_3 2 87 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 87
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 229
  (allA_of_3_1 86 86 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 229 (allA_succ_of_accept 84 85 229
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 84 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 229 (accept_3_3 83 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 82 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 229 (accept_3_3 80 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 229 (Polychromatic418967fa.accept_13_1_7_8_1_1796 79 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 229
  (Polychromatic418967fa.accept_19_2_9_1_1_4029 78 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 229 (accept_3_3 77 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 229 (Polychromatic418967fa.accept_13_10_7_8_1_1794 75 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 229 (accept_3_3 74 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 85 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 229
  (Polychromatic418967fa.accept_22_6_19_9_1_13681 72 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 229 (accept_3_3 71 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 229 (Polychromatic418967fa.accept_20_10_5_9_1_10908 70 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 229 (accept_3_3 68 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 229 (accept_3_3 65 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 229 (Polychromatic418967fa.accept_10_4_5_9_1_1231 64 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 229 (Polychromatic418967fa.accept_23_17_16_22_1_13680 63 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 229 (accept_3_3 62 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 85 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 229 (accept_3_3 59 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 58 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 229 (Polychromatic418967fa.accept_21_15_1_19_1_9205 57 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 229 (accept_3_3 56 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 85 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 229
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 229 (accept_3_3 53 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 229 (accept_3_3 50 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 229 (Polychromatic418967fa.accept_13_10_7_8_1_1794 49 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 229 (accept_3_3 47 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 229 (accept_3_3 44 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 229 (Polychromatic418967fa.accept_11_10_8_9_1_492 43 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 229
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 42 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 229 (accept_3_3 41 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 229 (Polychromatic418967fa.accept_13_1_7_8_1_1796 40 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 229 (accept_3_3 38 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 37 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 229
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 229 (accept_3_3 35 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 229 (Polychromatic418967fa.accept_19_14_9_1_1_8315 33 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 229 (accept_3_3 32 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 85 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 229
  (Polychromatic418967fa.accept_19_11_9_1_1_2809 30 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 229 (accept_3_3 29 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 229 (Polychromatic418967fa.accept_13_2_7_8_1_4221 28 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 229 (accept_3_3 26 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 229 (accept_3_3 23 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 229 (Polychromatic418967fa.accept_13_9_7_8_1_1122 22 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 229 (accept_3_3 20 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 229 (Polychromatic418967fa.accept_25_19_10_4_1_13679 19 85 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 229 (accept_3_3 17 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 229 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 229 (Polychromatic418967fa.accept_13_2_7_8_1_4221 15 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 229 (accept_3_3 14 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 229
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 229 (accept_3_3 11 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 229 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 229 (accept_3_3 8 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 85 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 229 (accept_3_3 5 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 85 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 85 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 229 (accept_3_3 2 85 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 85 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 229
  (allA_succ_of_accept 83 84 229 (accept_3_3 83 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 229 (accept_3_3 80 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 84 229 (accept_3_3 77 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  84 229 (Polychromatic418967fa.accept_13_11_6_8_1_1121 76 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 84 229 (Polychromatic418967fa.accept_10_5_4_9_1_420 75 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 229 (accept_3_3 74 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 229
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 72 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 229 (accept_3_3 71 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 229 (accept_3_3 68 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 229 (Polychromatic418967fa.accept_13_2_6_8_1_1092 67 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 229
  (Polychromatic418967fa.accept_13_1_6_8_1_208 66 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 84 229 (accept_3_3 65 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  84 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 229 (accept_3_3 62 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 229 (accept_3_3 59 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 229 (accept_3_3 56 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 229
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 54 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 229 (accept_3_3 53 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  84 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 229 (accept_3_3 50 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 229
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 229 (accept_3_3 47 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 229 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 229 (accept_3_3 44 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 229 (accept_3_3 41 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 229 (Polychromatic418967fa.accept_13_1_6_8_1_208 40 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 229 (Polychromatic418967fa.accept_18_3_12_13_1_3307 39 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 229 (accept_3_3 38 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 84 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 229
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 229 (accept_3_3 35 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 229 (accept_3_3 32 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 229 (Polychromatic418967fa.accept_16_15_4_5_1_1411 31 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 229
  (Polychromatic418967fa.accept_19_11_8_1_1_801 30 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 229 (accept_3_3 29 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 229 (accept_3_3 26 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 229 (accept_3_3 23 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 229 (Polychromatic418967fa.accept_16_6_4_5_1_2272 22 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 229 (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 229 (accept_3_3 20 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 229
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 229 (accept_3_3 17 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 229 (accept_3_3 14 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 229
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 229 (accept_3_3 11 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 229 (accept_3_3 8 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 229 (accept_3_3 5 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  229 (Polychromatic418967fa.accept_24_4_12_13_1_13678 4 84 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 84 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 229 (accept_3_3 2 84 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 229 (allA_of_3_1
  83 83 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 229 (allA_succ_of_accept 81 82 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 229 (accept_3_3 80 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 229 (accept_3_3 77 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 76 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 229 (accept_3_3 74 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 73 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 229 (Polychromatic418967fa.accept_15_12_7_4_1_2921 72 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 229 (accept_3_3 71 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 82 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 229 (accept_3_3 68 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 229 (accept_3_3 65 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 229 (accept_3_3 62 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 229 (accept_3_3 59 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 229 (Polychromatic418967fa.accept_17_7_14_8_1_5069 58 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 229 (accept_3_3 56 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 229 (Polychromatic418967fa.accept_23_8_13_22_1_13677 54 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 229 (accept_3_3 53 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 82 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 229 (accept_3_3 50 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 229 (Polychromatic418967fa.accept_13_10_4_8_1_2570 49 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 229 (accept_3_3 47 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 229 (Polychromatic418967fa.accept_22_2_16_9_1_13676 46 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 229 (accept_3_3 44 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 229 (accept_3_3 41 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 229 (accept_3_3 38 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 229 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 229 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 229 (accept_3_3 35 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 82 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 229 (accept_3_3 32 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 229 (accept_3_3 29 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 229 (accept_3_3 26 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 229 (accept_3_3 23 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 229 (Polychromatic418967fa.accept_13_9_4_8_1_1752 22 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 229 (accept_3_3 20 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 229 (accept_3_3 17 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 229 (accept_3_3 14 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 229 (Polychromatic418967fa.accept_16_13_2_5_1_3336 13 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 229 (accept_3_3 11 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 229 (Polychromatic418967fa.accept_13_10_4_8_1_2570 10 82 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 229 (accept_3_3 8 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 82 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 229 (accept_3_3 5 82 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 82 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 229 (accept_3_3 2 82 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 1
  82 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 229
  (allA_succ_of_accept 80 81 229 (accept_3_3 80 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 229 (accept_3_3 77 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 229
  (Polychromatic418967fa.accept_10_5_1_9_1_791 75 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 229 (accept_3_3 74 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 229 (Polychromatic418967fa.accept_15_13_6_4_1_1221 73 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 229 (accept_3_3 71 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 229 (accept_3_3 68 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 229 (Polychromatic418967fa.accept_21_4_18_19_1_9189 67 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 229 (Polychromatic418967fa.accept_17_15_13_8_1_7603 66 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 229 (accept_3_3 65 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 229 (accept_3_3 62 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 229 (Polychromatic418967fa.accept_13_9_3_8_1_573 61 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 229 (accept_3_3 59 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 229 (accept_3_3 56 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 229 (Polychromatic418967fa.accept_15_9_6_4_1_1220 54 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 229 (accept_3_3 53 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 229 (accept_3_3 50 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 229 (Polychromatic418967fa.accept_17_15_13_8_1_7603 49 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 229 (accept_3_3 47 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 229
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 229 (accept_3_3 44 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 229 (accept_3_3 41 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 229 (accept_3_3 38 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 229 (accept_3_3 35 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 229
  (Polychromatic418967fa.accept_13_7_3_8_1_1750 33 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 229 (accept_3_3 32 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 229 (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 229 (accept_3_3 29 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 229 (accept_3_3 26 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 229 (accept_3_3 23 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 229
  (Polychromatic418967fa.accept_17_4_13_8_1_3874 21 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 229 (accept_3_3 20 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 229 (Polychromatic418967fa.accept_25_19_6_4_1_13675 19 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 229 (accept_3_3 17 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 229 (accept_3_3 14 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 229 (accept_3_3 11 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 229 (accept_3_3 8 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  229 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 229 (accept_3_3 5 81 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 229 (accept_3_3 2 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 81 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 229
  (allA_of_3_1 80 80 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 229 (allA_succ_of_accept 78 79 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 229 (accept_3_3 77 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 229 (Polychromatic418967fa.accept_13_11_1_8_1_1776 76 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 229 (accept_3_3 74 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 229
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 72 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 229 (accept_3_3 71 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 229 (accept_3_3 68 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 229 (accept_3_3 65 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 229 (Polychromatic418967fa.accept_13_11_1_8_1_1776 63 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 229 (accept_3_3 62 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 229 (Polychromatic418967fa.accept_13_9_1_8_1_1742 61 79 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 229 (accept_3_3 59 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 229 (accept_3_3 56 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 229 (accept_3_3 53 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 229 (accept_3_3 50 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 229 (Polychromatic418967fa.accept_14_7_9_5_1_529 49 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 229 (accept_3_3 47 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 229 (accept_3_3 44 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 229 (Polychromatic418967fa.accept_17_9_11_8_1_5077 43 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 229 (accept_3_3 41 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 229 (accept_3_3 38 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 229
  (Polychromatic418967fa.accept_16_4_15_5_1_5537 36 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 229 (accept_3_3 35 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 229 (accept_3_3 32 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 229 (accept_3_3 29 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 229 (Polychromatic418967fa.accept_28_27_23_5_1_13674 27 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 229 (accept_3_3 26 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 79 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 229 (accept_3_3 23 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 229 (accept_3_3 20 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 229 (accept_3_3 17 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 229 (Polychromatic418967fa.accept_19_16_3_1_1_5389 16 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 229 (accept_3_3 14 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 229 (Polychromatic418967fa.accept_20_13_19_9_1_10976 13 79 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 229 (accept_3_3 11 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 229 (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 229 (accept_3_3 8 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 79 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 229 (accept_3_3 5 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 79 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 79 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 229 (accept_3_3 2 79 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 79 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 229
  (allA_succ_of_accept 77 78 229 (accept_3_3 77 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 229 (accept_3_3 74 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 229
  (Polychromatic418967fa.accept_19_15_2_1_1_2822 72 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 229 (accept_3_3 71 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 229 (accept_3_3 68 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 229 (accept_3_3 65 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 229 (accept_3_3 62 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 229 (accept_3_3 59 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 229 (Polychromatic418967fa.accept_16_10_14_5_1_5496 58 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 229 (accept_3_3 56 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 229
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 229 (accept_3_3 53 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 229 (accept_3_3 50 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 229 (Polychromatic418967fa.accept_17_15_10_8_1_1708 49 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 229 (accept_3_3 47 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 229 (accept_3_3 44 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 229
  (Polychromatic418967fa.accept_16_10_14_5_1_5496 42 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 229 (accept_3_3 41 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 229 (Polychromatic418967fa.accept_24_16_6_13_1_13661 40 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 229 (accept_3_3 38 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 229
  (Polychromatic418967fa.accept_17_2_10_8_1_7691 36 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 229 (accept_3_3 35 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 229 (Polychromatic418967fa.accept_19_14_2_1_1_8308 33 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 229 (accept_3_3 32 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 229 (accept_3_3 29 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 229 (accept_3_3 26 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 229 (accept_3_3 23 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 229 (Polychromatic418967fa.accept_15_7_3_4_1_574 22 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 229 (accept_3_3 20 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 229 (accept_3_3 17 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 229 (accept_3_3 14 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 229 (accept_3_3 11 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 229 (Polychromatic418967fa.accept_16_9_14_5_1_2239 9 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 229 (accept_3_3 8 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 229 (accept_3_3 5 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 78 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 229 (accept_3_3 2 78 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 229 (allA_of_3_1 77 77
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 229 (allA_succ_of_accept 75 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 229 (accept_3_3 74 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 229 (Polychromatic418967fa.accept_15_12_1_4_1_2899 72 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 229 (accept_3_3 71 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 76
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 229 (accept_3_3 68 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 229 (Polychromatic418967fa.accept_13_1_11_8_1_2562 66 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 229 (accept_3_3 65 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 76 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 229 (accept_3_3 62 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 229 (Polychromatic418967fa.accept_13_9_11_8_1_195 61 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 229 (accept_3_3 59 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 229 (accept_3_3 56 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 229 (Polychromatic418967fa.accept_10_5_6_9_1_2235 55 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 229 (Polychromatic418967fa.accept_23_8_7_22_1_13673 54 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 229 (accept_3_3 53 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 52 76
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 229 (accept_3_3 50 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 229 (Polychromatic418967fa.accept_13_9_11_8_1_195 48 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 229 (accept_3_3 47 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 229 (accept_3_3 44 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 229 (Polychromatic418967fa.accept_13_3_11_8_1_1094 42 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 229 (accept_3_3 41 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 229 (Polychromatic418967fa.accept_13_1_11_8_1_2562 40 76
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 229 (accept_3_3 38 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 229 (Polychromatic418967fa.accept_21_16_13_19_1_6035 37 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 229 (accept_3_3 35 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 229 (Polychromatic418967fa.accept_11_1_10_9_1_871 34 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 229 (accept_3_3 32 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 229 (Polychromatic418967fa.accept_23_8_7_22_1_13673 31 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 229 (accept_3_3 29 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 229 (Polychromatic418967fa.accept_18_10_4_13_1_3296 28 76
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 229 (accept_3_3 26 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 229 (Polychromatic418967fa.accept_16_8_12_5_1_200 24 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 229 (accept_3_3 23 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 229 (accept_3_3 20 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 229 (accept_3_3 17 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 229 (Polychromatic418967fa.accept_13_3_11_8_1_1094 16 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 229 (accept_3_3 14 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 229 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 229 (accept_3_3 11 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 229 (accept_3_3 8 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  229 (Polychromatic418967fa.accept_16_7_12_5_1_734 7 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 76 229 (Polychromatic418967fa.accept_13_6_11_8_1_1111 6 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 229 (accept_3_3 5 76 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 76 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 76 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 76 229 (accept_3_3 2 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76
  229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 76 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 229
  (allA_succ_of_accept 74 75 229 (accept_3_3 74 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  75 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 75 229 (Polychromatic418967fa.accept_13_7_10_8_1_567 72 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 229 (accept_3_3 71 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 229 (accept_3_3 68 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  75 229 (Polychromatic418967fa.accept_13_2_10_8_1_1126 67 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 229 (accept_3_3 65 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 229
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 63 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 75 229 (accept_3_3 62 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  75 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 75 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 229 (accept_3_3 59 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 229 (accept_3_3 56 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  75 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 229 (accept_3_3 53 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 75 229 (accept_3_3 50 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  75 229 (Polychromatic418967fa.accept_19_11_18_1_1_4048 49 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 75 229 (Polychromatic418967fa.accept_17_14_7_8_1_7544 48 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 229 (accept_3_3 47 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 229 (accept_3_3 44 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 229 (accept_3_3 41 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 229
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 39 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 229 (accept_3_3 38 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 229 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 229 (accept_3_3 35 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 229 (accept_3_3 32 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 229 (accept_3_3 29 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 229
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 27 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 229 (accept_3_3 26 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 229 (accept_3_3 23 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 229
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 229 (accept_3_3 20 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 229 (accept_3_3 17 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 229 (accept_3_3 14 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 229 (Polychromatic418967fa.accept_19_13_18_1_1_8215 13 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 229 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 229 (accept_3_3 11 75 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 229 (accept_3_3 8 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 229 (accept_3_3 5 75 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 229 (Polychromatic418967fa.accept_20_3_15_9_1_6456
  3 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 229 (accept_3_3 2 75
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 229 (Polychromatic418967fa.accept_9_1_3_4_1_47
  1 75 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 229 (allA_of_3_1 74 74
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 229 (allA_succ_of_accept 72 73 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 72 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 229 (accept_3_3 71 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 229 (accept_3_3 68 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 229 (Polychromatic418967fa.accept_19_10_16_1_1_8271 67 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 229 (accept_3_3 65 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 229 (Polychromatic418967fa.accept_17_12_5_8_1_7680 63 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 229 (accept_3_3 62 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 73 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 229 (accept_3_3 59 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 229 (accept_3_3 56 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 229 (Polychromatic418967fa.accept_15_10_13_4_1_1210 55 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 229
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 229 (accept_3_3 53 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 229 (accept_3_3 50 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 229 (accept_3_3 47 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 46 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 229 (Polychromatic418967fa.accept_16_13_9_5_1_3302 45 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 229 (accept_3_3 44 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 73 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 229 (accept_3_3 41 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 229 (Polychromatic418967fa.accept_14_12_3_5_1_1868 40 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 229 (accept_3_3 38 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 229 (accept_3_3 35 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 229 (accept_3_3 32 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 229 (Polychromatic418967fa.accept_23_8_4_22_1_8781 31 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 229 (accept_3_3 29 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 229 (accept_3_3 26 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 229 (accept_3_3 23 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 229 (accept_3_3 20 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 229 (Polychromatic418967fa.accept_20_19_13_9_1_5019 19 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 229
  (Polychromatic418967fa.accept_23_18_4_22_1_13672 18 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 73 229 (accept_3_3 17 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 73 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 73 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 73 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 229 (accept_3_3 14 73 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 229 (Polychromatic418967fa.accept_11_2_7_9_1_890
  13 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 229 (accept_3_3 11 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 229 (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 229 (accept_3_3 8 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 229 (accept_3_3 5 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  229 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 73 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 73 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 229 (accept_3_3 2 73 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 229 (allA_succ_of_accept 71
  72 229 (accept_3_3 71 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 229
  (Polychromatic418967fa.accept_21_7_9_19_1_13671 70 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 229 (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 72 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 229 (accept_3_3 68 72 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 66
  72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 229 (accept_3_3 65 72
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 229
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 64 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 72 229 (Polychromatic418967fa.accept_14_7_2_5_1_4528 63 72 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 229 (accept_3_3 62 72 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 72 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 61 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 60
  72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 229 (accept_3_3 59 72
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 72 229
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 72 229 (Polychromatic418967fa.accept_10_7_2_9_1_775 57 72 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 229 (accept_3_3 56 72 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 72 229 (Polychromatic418967fa.accept_13_3_7_8_1_4192 55 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 229 (Polychromatic418967fa.accept_13_2_7_8_1_4221
  54 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 229 (accept_3_3 53
  72 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 52 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 72 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 72 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 229 (accept_3_3 50 72 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 72 229 (Polychromatic418967fa.accept_13_10_7_8_1_1794 49 72 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 229
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 48 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 229 (accept_3_3 47 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 229 (accept_3_3 44 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 229 (Polychromatic418967fa.accept_16_11_8_5_1_4366 43 72 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 229
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 42 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 229 (accept_3_3 41 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 229 (Polychromatic418967fa.accept_13_1_7_8_1_1796 40 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 229 (accept_3_3 38 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 229 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 72 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 229
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 229 (accept_3_3 35 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 229 (Polychromatic418967fa.accept_23_11_3_22_1_13670 34 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 229 (Polychromatic418967fa.accept_19_14_15_1_1_6806 33 72 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 229 (accept_3_3 32 72 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 72 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 229
  (Polychromatic418967fa.accept_17_13_4_8_1_3830 30 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 229 (accept_3_3 29 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 229 (Polychromatic418967fa.accept_13_2_7_8_1_4221 28 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 229 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 229 (accept_3_3 26 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 72 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 229 (accept_3_3 23 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 229 (Polychromatic418967fa.accept_13_9_7_8_1_1122 22 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 229 (accept_3_3 20 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 229 (Polychromatic418967fa.accept_16_3_8_5_1_6790 19 72 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 229 (accept_3_3 17 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 229 (Polychromatic418967fa.accept_13_3_7_8_1_4192 16 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 229 (Polychromatic418967fa.accept_13_2_7_8_1_4221 15 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 229 (accept_3_3 14 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 229 (Polychromatic418967fa.accept_16_13_8_5_1_3298 13 72 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 229
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 229 (accept_3_3 11 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 229 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 229 (accept_3_3 8 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 229 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 72 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 229
  (Polychromatic418967fa.accept_25_6_22_4_1_13669 6 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 229 (accept_3_3 5 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 72 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 72 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 229 (accept_3_3 2 72 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 72 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 72 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 229 (allA_of_3_1 71 71 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 229 (allA_succ_of_accept 69 70 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 229 (accept_3_3 68 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 229 (accept_3_3 65 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 229 (accept_3_3 62 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 229 (Polychromatic418967fa.accept_17_10_2_8_1_6295 61 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 229 (accept_3_3 59 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 58 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 229 (accept_3_3 56 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 229 (Polychromatic418967fa.accept_15_9_10_4_1_2055 54 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 229 (accept_3_3 53 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 70 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 229 (accept_3_3 50 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 229 (Polychromatic418967fa.accept_13_10_5_8_1_2555 49 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 229 (accept_3_3 47 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 229 (accept_3_3 44 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 229 (accept_3_3 41 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 229 (accept_3_3 38 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 229 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 229 (accept_3_3 35 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 229 (Polychromatic418967fa.accept_21_13_7_19_1_4505 34 70
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 229 (accept_3_3 32 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 229 (accept_3_3 29 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 229 (accept_3_3 26 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 229 (Polychromatic418967fa.accept_13_12_5_8_1_1101 25 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 229 (accept_3_3 23 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 229 (accept_3_3 20 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 229 (Polychromatic418967fa.accept_19_18_13_1_1_9735 18 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 229 (accept_3_3 17 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 70 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 229 (accept_3_3 14 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 229 (accept_3_3 11 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 70 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 229 (accept_3_3 8 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 70 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 229 (accept_3_3 5 70 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 70 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 70 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 229 (accept_3_3 2 70 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 229 (allA_succ_of_accept 68 69
  229 (accept_3_3 68 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 67 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 69 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 229 (accept_3_3 65 69 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 229 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 229 (accept_3_3 62
  69 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 229
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 69 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 69 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 229 (accept_3_3 59 69 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 69 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 57
  69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 229 (accept_3_3 56 69
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 229 (Polychromatic418967fa.accept_9_1_6_4_1_49
  55 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 229
  (Polychromatic418967fa.accept_21_12_6_19_1_1871 54 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 69 229 (accept_3_3 53 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  69 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 229 (accept_3_3 50 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 229 (Polychromatic418967fa.accept_13_10_4_8_1_2570 49 69 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 69 229 (accept_3_3 47 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  69 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 229 (Polychromatic418967fa.accept_17_11_1_8_1_7502 45 69 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 229 (accept_3_3 44 69 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 69 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 229
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 42 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 229 (accept_3_3 41 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  69 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 229 (accept_3_3 38 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 69 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 229 (accept_3_3 35 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  69 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 229 (Polychromatic418967fa.accept_21_12_6_19_1_1871 33 69 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 229 (accept_3_3 32 69 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 229 (Polychromatic418967fa.accept_24_7_21_13_1_13668 31 69
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 229 (accept_3_3 29 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 229 (accept_3_3 26 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 69 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 229
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 24 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 229 (accept_3_3 23 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  69 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 229 (accept_3_3 20 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 69 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 229 (accept_3_3 17 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 229 (accept_3_3 14 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 229 (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 69 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 229 (accept_3_3 11 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 229 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 229 (accept_3_3 8 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 69 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 229
  (Polychromatic418967fa.accept_11_6_3_9_1_906 6 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 229 (accept_3_3 5 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 69 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 229 (accept_3_3 2 69 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 69 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 229 (allA_of_3_1 68 68 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 229 (allA_succ_of_accept 66 67 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 229 (accept_3_3 65 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 229 (Polychromatic418967fa.accept_15_3_7_4_1_1225 63 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 229 (accept_3_3 62 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 229 (Polychromatic418967fa.accept_19_4_10_1_1_2776 61 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 229
  (Polychromatic418967fa.accept_17_9_16_8_1_2721 60 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 229 (accept_3_3 59 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 229 (accept_3_3 56 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 229 (accept_3_3 53 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 229 (Polychromatic418967fa.accept_10_2_7_9_1_783 52 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 229 (accept_3_3 50 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 229 (Polychromatic418967fa.accept_13_10_2_8_1_2603 49 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 229 (accept_3_3 47 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 229 (accept_3_3 44 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 229 (accept_3_3 41 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 229 (Polychromatic418967fa.accept_15_10_7_4_1_1222 40 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 229 (Polychromatic418967fa.accept_21_18_4_19_1_1838 39 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 229 (accept_3_3 38 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 67 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 229 (accept_3_3 35 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 229 (Polychromatic418967fa.accept_13_7_2_8_1_1746 33 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 229 (accept_3_3 32 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 229 (Polychromatic418967fa.accept_17_14_16_8_1_3861 31 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 229 (accept_3_3 29 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 229 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 229 (accept_3_3 26 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 229 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 229
  (Polychromatic418967fa.accept_16_8_3_5_1_5512 24 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 229 (accept_3_3 23 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 229 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 229 (accept_3_3 20 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 67 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 229 (accept_3_3 17 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 229 (accept_3_3 14 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 229
  (Polychromatic418967fa.accept_10_2_7_9_1_783 12 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 229 (accept_3_3 11 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 229 (accept_3_3 8 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 229 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 229 (accept_3_3 5 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  229 (Polychromatic418967fa.accept_19_4_10_1_1_2776 4 67 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 229 (Polychromatic418967fa.accept_15_3_7_4_1_1225 3 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 229 (accept_3_3 2 67 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 67 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 229 (allA_succ_of_accept 65 66
  229 (accept_3_3 65 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 64 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 229 (accept_3_3 62 66 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 60
  66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 229 (accept_3_3 59 66
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 229 (Polychromatic418967fa.accept_7_2_3_5_1_34
  58 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 66 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 66 229 (accept_3_3 56 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  66 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 66 229 (Polychromatic418967fa.accept_14_12_10_5_1_2712 54 66 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 229 (accept_3_3 53 66 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 66 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 66 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 66 229 (accept_3_3 50 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  66 229 (Polychromatic418967fa.accept_19_11_9_1_1_2809 49 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 66 229 (Polychromatic418967fa.accept_13_9_1_8_1_1742 48 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 229 (accept_3_3 47 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 66 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 66 229
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 66 229 (accept_3_3 44 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  66 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 66 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 229 (accept_3_3 41 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 229 (Polychromatic418967fa.accept_14_12_10_5_1_2712 40 66 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 66 229 (accept_3_3 38 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  66 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 66 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 229 (accept_3_3 35 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 66 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 66 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 66 229 (accept_3_3 32 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  66 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 66 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 229 (accept_3_3 29 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 66 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 66 229 (accept_3_3 26 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  66 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 66 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 229 (accept_3_3 23 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 66 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 229
  (Polychromatic418967fa.accept_18_3_12_13_1_3307 21 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 66 229 (accept_3_3 20 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  66 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 66 229 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 229 (accept_3_3 17 66 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 66 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 229 (accept_3_3 14 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  66 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 229 (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 66 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 229 (accept_3_3 11 66 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 66 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 229 (accept_3_3 8 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66
  229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 66 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 229 (accept_3_3 5 66 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 229 (Polychromatic418967fa.accept_27_4_12_13_1_13667 4 66 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 229 (accept_3_3 2 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66
  229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 66 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 229 (allA_of_3_1 65
  65 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 229 (allA_succ_of_accept 63 64 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 229 (accept_3_3 62 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 229 (accept_3_3 59 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 64 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 229 (accept_3_3 56 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 229 (Polychromatic418967fa.accept_17_3_13_8_1_11337 54 64 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 229 (accept_3_3 53 64 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 64 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 229 (accept_3_3 50 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 229 (Polychromatic418967fa.accept_13_10_12_8_1_2550 49 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 229 (accept_3_3 47 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 64 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 229 (accept_3_3 44 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 229 (accept_3_3 41 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 229 (Polychromatic418967fa.accept_13_1_12_8_1_1818 40 64 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 229 (accept_3_3 38 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 229 (Polychromatic418967fa.accept_17_3_13_8_1_11337 37 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 229 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 64 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 229 (accept_3_3 35 64 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 64 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 229 (accept_3_3 32 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 229 (accept_3_3 29 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 64 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 229 (accept_3_3 26 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 229 (accept_3_3 23 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 64 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 229 (accept_3_3 20 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 229 (Polychromatic418967fa.accept_18_1_10_13_1_500 19 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 229 (accept_3_3 17 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 64 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 229 (accept_3_3 14 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 229 (accept_3_3 11 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 64 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 229 (accept_3_3 8 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 64 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 229 (accept_3_3 5 64 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 64 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 229 (accept_3_3 2 64 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 229 (Polychromatic418967fa.accept_13_1_12_8_1_1818
  1 64 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 229 (allA_succ_of_accept 62 63 229
  (accept_3_3 62 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 229
  (Polychromatic418967fa.accept_13_9_11_8_1_195 61 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 229 (Polychromatic418967fa.accept_18_6_9_13_1_3320 60 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 229 (accept_3_3 59 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 229 (Polychromatic418967fa.accept_12_9_3_1_1_303
  57 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 229 (accept_3_3 56
  63 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 229
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 55 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 229 (accept_3_3 53 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 63 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 229 (Polychromatic418967fa.accept_14_9_7_5_1_1105
  51 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 229 (accept_3_3 50
  63 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 229
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 49 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 63 229 (Polychromatic418967fa.accept_13_9_11_8_1_195 48 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 229 (accept_3_3 47 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 63 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 229 (Polychromatic418967fa.accept_12_9_3_1_1_303
  45 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 229 (accept_3_3 44
  63 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 229
  (Polychromatic418967fa.accept_11_10_8_9_1_492 43 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 63 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 229 (accept_3_3 41 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 63 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 229 (Polychromatic418967fa.accept_17_5_12_8_1_6304
  39 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 229 (accept_3_3 38
  63 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 229
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 63 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 229 (accept_3_3 35 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 63 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 229 (Polychromatic418967fa.accept_12_9_3_1_1_303
  33 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 229 (accept_3_3 32
  63 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 229
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 31 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 63 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 229 (accept_3_3 29 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 63 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 229 (Polychromatic418967fa.accept_13_1_11_8_1_2562
  27 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 229 (accept_3_3 26
  63 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 229
  (Polychromatic418967fa.accept_36_25_27_13_1_13666 25 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 63 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 229 (accept_3_3 23 63 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 229
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 229 (accept_3_3 20 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 229 (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 229 (accept_3_3 17 63 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 229
  (Polychromatic418967fa.accept_20_15_3_9_1_5007 15 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 229 (accept_3_3 14 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 229 (Polychromatic418967fa.accept_26_13_11_21_1_13665 13 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 229 (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 63 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 229 (accept_3_3 11 63 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 229 (accept_3_3 8 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  229 (Polychromatic418967fa.accept_15_7_3_4_1_574 7 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 229 (accept_3_3 5 63 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 229 (Polychromatic418967fa.accept_13_3_11_8_1_1094
  3 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 229 (accept_3_3 2 63
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 229
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 63 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 229 (allA_of_3_1 62 62
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 229 (allA_succ_of_accept 60 61 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 229 (accept_3_3 59 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 58 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 229 (accept_3_3 56 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 61 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 229
  (Polychromatic418967fa.accept_19_16_4_1_1_5376 54 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 229 (accept_3_3 53 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 52 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 229 (accept_3_3 50 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 229 (Polychromatic418967fa.accept_16_1_13_5_1_2280 49 61 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 229 (accept_3_3 47 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 229 (accept_3_3 44 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 229 (Polychromatic418967fa.accept_13_4_9_8_1_1736 43 61 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 229 (accept_3_3 41 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 229 (Polychromatic418967fa.accept_13_1_9_8_1_1734 40 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 229 (accept_3_3 38 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 61 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 229
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 229 (accept_3_3 35 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 229 (Polychromatic418967fa.accept_16_2_13_5_1_2257 34 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 229 (accept_3_3 32 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 229 (Polychromatic418967fa.accept_19_12_4_1_1_8252 31 61 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 229 (accept_3_3 29 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 229 (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 229 (accept_3_3 26 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 61 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 229 (accept_3_3 23 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 229 (accept_3_3 20 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 229
  (Polychromatic418967fa.accept_10_8_1_9_1_413 18 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 229 (accept_3_3 17 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 229 (Polychromatic418967fa.accept_13_3_9_8_1_4202 16 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 229 (accept_3_3 14 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 229 (Polychromatic418967fa.accept_31_13_30_12_1_13664 13 61 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 229 (accept_3_3 11 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 229 (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 229 (accept_3_3 8 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 229 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 61 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 229 (accept_3_3 5 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  229 (Polychromatic418967fa.accept_13_4_9_8_1_1736 4 61 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 229 (accept_3_3 2 61 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 61 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 229 (allA_succ_of_accept 59 60 229
  (accept_3_3 59 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 58 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 60 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 229 (accept_3_3 56 60 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 60 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 229 (Polychromatic418967fa.accept_19_16_3_1_1_5389
  54 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 229 (accept_3_3 53
  60 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 229
  (Polychromatic418967fa.accept_9_7_6_4_1_483 52 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 60 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 229 (accept_3_3 50 60 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 60 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 48
  60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 229 (accept_3_3 47 60
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 229 (Polychromatic418967fa.accept_9_1_6_4_1_49
  46 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 60 229
  (Polychromatic418967fa.accept_17_11_9_8_1_5038 45 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 60 229 (accept_3_3 44 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  60 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 60 229 (Polychromatic418967fa.accept_16_10_12_5_1_2254 42 60 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 229 (accept_3_3 41 60 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 60 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 60 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 60 229 (accept_3_3 38 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  60 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 60 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 229 (accept_3_3 35 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 60 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 229
  (Polychromatic418967fa.accept_8_1_4_5_1_48 33 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 60 229 (accept_3_3 32 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  60 229 (Polychromatic418967fa.accept_23_8_14_22_1_12013 31 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 60 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 229 (accept_3_3 29 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 60 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 60 229 (accept_3_3 26 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  60 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 60 229 (Polychromatic418967fa.accept_16_8_12_5_1_200 24 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 229 (accept_3_3 23 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 60 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 60 229 (accept_3_3 20 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  60 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 60 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 229 (accept_3_3 17 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 60 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 60 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 60 229 (accept_3_3 14 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  60 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 60 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 229 (accept_3_3 11 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 60 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 60 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 60 229 (accept_3_3 8 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60
  229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 60 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 60 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 229 (accept_3_3 5 60 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 60 229 (Polychromatic418967fa.accept_16_4_12_5_1_2287 4 60 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  60 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 229 (accept_3_3 2 60 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 229 (allA_of_3_1 59 59 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 229 (allA_succ_of_accept 57 58 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 229 (accept_3_3 56 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 58 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 229 (accept_3_3 53 58 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 229 (accept_3_3 50 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 229 (Polychromatic418967fa.accept_14_7_2_5_1_4528 49 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 229 (Polychromatic418967fa.accept_17_14_7_8_1_7544 48 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 229 (accept_3_3 47 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 58 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 229 (accept_3_3 44 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 229 (Polychromatic418967fa.accept_22_20_14_9_1_12125 42 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 229 (accept_3_3 41 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 58 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 229 (accept_3_3 38 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 229 (Polychromatic418967fa.accept_10_7_8_9_1_785 37 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 229 (Polychromatic418967fa.accept_15_6_13_4_1_2040 36 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 229 (accept_3_3 35 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 58 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 229 (accept_3_3 32 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 229 (Polychromatic418967fa.accept_16_14_10_5_1_1393 30 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 229 (accept_3_3 29 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 28 58 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 229 (accept_3_3 26 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 58 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 229 (accept_3_3 23 58 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 229 (Polychromatic418967fa.accept_21_1_16_19_1_3134 22 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 229 (accept_3_3 20 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 58 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 229 (accept_3_3 17 58 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 229 (accept_3_3 14 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 229 (Polychromatic418967fa.accept_16_13_10_5_1_2278 13 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 229 (Polychromatic418967fa.accept_16_12_10_5_1_5457 12 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 229 (accept_3_3 11 58 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 58 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 229 (accept_3_3 8 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 58 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 229 (accept_3_3 5 58 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 58 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 229 (accept_3_3 2 58 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 1
  58 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 229 (allA_succ_of_accept 56 57 229
  (accept_3_3 56 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 229 (Polychromatic418967fa.accept_15_9_12_4_1_2023 54 57 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 229 (accept_3_3 53 57 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 51
  57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 229 (accept_3_3 50 57
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 229
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 49 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 229 (accept_3_3 47 57 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 45
  57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 229 (accept_3_3 44 57
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 229
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 57 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 229 (accept_3_3 41 57 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 39
  57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 229 (accept_3_3 38 57
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 229 (Polychromatic418967fa.accept_9_1_3_4_1_47
  37 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 229 (accept_3_3 35 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 229 (accept_3_3 32 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 57 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 229
  (Polychromatic418967fa.accept_16_14_9_5_1_4388 30 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 229 (accept_3_3 29 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 229 (accept_3_3 26 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 57 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 229 (accept_3_3 23 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 229 (Polychromatic418967fa.accept_22_21_13_9_1_5675 21 57 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 229 (accept_3_3 20 57 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 57 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 229 (accept_3_3 17 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 229 (accept_3_3 14 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 57 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 229 (accept_3_3 11 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 229 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 229 (accept_3_3 8 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 57 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 229 (accept_3_3 5 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 57 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 229 (accept_3_3 2 57 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 57 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 229 (allA_of_3_1 56 56 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 229
  (allA_succ_of_accept 54 55 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 229 (accept_3_3 53 55 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 51
  55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 229 (accept_3_3 50 55
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 229
  (Polychromatic418967fa.accept_21_7_13_19_1_4477 49 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 229 (accept_3_3 47 55 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 229 (Polychromatic418967fa.accept_20_5_15_9_1_9446
  45 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 229 (accept_3_3 44
  55 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 55 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 229 (accept_3_3 41 55 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 55 229 (Polychromatic418967fa.accept_24_16_7_13_1_13663 40 55 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 229 (accept_3_3 38 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 229 (Polychromatic418967fa.accept_13_11_3_8_1_1786 37 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 229 (accept_3_3 35 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 229 (accept_3_3 32 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 229 (accept_3_3 29 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 55 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 229
  (Polychromatic418967fa.accept_16_11_7_5_1_4364 27 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 229 (accept_3_3 26 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 229 (accept_3_3 23 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 229 (accept_3_3 20 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 229 (Polychromatic418967fa.accept_22_19_11_9_1_9028 19 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 229 (accept_3_3 17 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 55 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 229 (accept_3_3 14 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 229 (accept_3_3 11 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 229
  (Polychromatic418967fa.accept_13_9_3_8_1_573 9 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 229 (accept_3_3 8 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 229 (accept_3_3 5 55 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 55 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  55 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 229 (accept_3_3 2 55 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 55
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 229 (allA_succ_of_accept 53 54 229
  (accept_3_3 53 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 229
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 52 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 54 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 229 (accept_3_3 50 54 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 54 229 (Polychromatic418967fa.accept_13_10_2_8_1_2603 49 54 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 229
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 229 (accept_3_3 47 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 229 (Polychromatic418967fa.accept_13_7_2_8_1_1746 46 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 229 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 229 (accept_3_3 44 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 229
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 42 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 229 (accept_3_3 41 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 229 (Polychromatic418967fa.accept_15_10_9_4_1_2924 40 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 229 (accept_3_3 38 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 229 (Polychromatic418967fa.accept_23_14_8_22_1_13662 37 54 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 229
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 229 (accept_3_3 35 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 229 (Polychromatic418967fa.accept_11_1_10_9_1_871 34 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 229 (accept_3_3 32 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 229
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 229 (accept_3_3 29 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 229 (accept_3_3 26 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 229 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 54 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 229
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 229 (accept_3_3 23 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 229 (Polychromatic418967fa.accept_17_5_3_8_1_1697 22 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 229 (Polychromatic418967fa.accept_14_7_12_5_1_1861 21 54 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 229 (accept_3_3 20 54 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 229
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 229 (accept_3_3 17 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 229 (Polychromatic418967fa.accept_24_16_6_13_1_13661 16 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 229 (accept_3_3 14 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 54 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 229
  (Polychromatic418967fa.accept_11_1_10_9_1_871 12 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 229 (accept_3_3 11 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 229 (Polychromatic418967fa.accept_13_10_2_8_1_2603 10 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 229 (Polychromatic418967fa.accept_21_9_12_19_1_12172 9 54 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 229 (accept_3_3 8 54 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 229
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 229 (accept_3_3 5 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  229 (Polychromatic418967fa.accept_16_4_6_5_1_2245 4 54 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 229 (accept_3_3 2 54 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 229 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 54 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 229 (allA_of_3_1 53 53 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 229 (allA_succ_of_accept 51 52 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 229 (accept_3_3 50 52 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 49
  52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 229 (accept_3_3 47 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 229 (accept_3_3 44 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 52 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 229 (accept_3_3 41 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 229 (Polychromatic418967fa.accept_14_12_10_5_1_2712 40 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 229 (accept_3_3 38 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 52 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 229 (accept_3_3 35 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 229 (accept_3_3 32 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 52 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 229 (accept_3_3 29 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 229 (accept_3_3 26 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 52 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 229 (accept_3_3 23 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 229 (accept_3_3 20 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 52 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 229
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 229 (accept_3_3 17 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 229 (accept_3_3 14 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 229 (Polychromatic418967fa.accept_19_13_14_1_1_3996 13 52 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 229 (accept_3_3 11 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 229 (accept_3_3 8 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 229 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 52 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 229 (accept_3_3 5 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  229 (Polychromatic418967fa.accept_17_4_1_8_1_5070 4 52 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 229 (accept_3_3 2 52 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 52 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  229)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 229 (allA_succ_of_accept 50 51 229 (accept_3_3
  50 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 229
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 51 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 229 (accept_3_3 47 51 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 45
  51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 229 (accept_3_3 44 51
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 229
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 229 (accept_3_3 41 51 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 39
  51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 229 (accept_3_3 38 51
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 229 (Polychromatic418967fa.accept_9_1_6_4_1_49
  37 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 229
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 229 (accept_3_3 35 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 229 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 229 (accept_3_3 32 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 51 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 229 (accept_3_3 29 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 229 (accept_3_3 26 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 51 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 229 (accept_3_3 23 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 229 (accept_3_3 20 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 51 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 229 (accept_3_3 17 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 229 (accept_3_3 14 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 229 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 51 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 229 (accept_3_3 11 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 229 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 229 (accept_3_3 8 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 51 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 229 (accept_3_3 5 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 229 (accept_3_3 2 51 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 51 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 229)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 229 (allA_of_3_1 50 50 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 229
  (allA_succ_of_accept 48 49 229 (Polychromatic418967fa.accept_19_10_11_1_1_8318 48 49 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 229 (accept_3_3 47 49 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 229 (Polychromatic418967fa.accept_13_7_10_8_1_567 46 49 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 229 (Polychromatic418967fa.accept_16_13_1_5_1_5469
  45 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 229 (accept_3_3 44
  49 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 229
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 43 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 229 (Polychromatic418967fa.accept_23_19_3_22_1_13660 42 49 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 229 (accept_3_3 41 49 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 49 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 229
  (Polychromatic418967fa.accept_21_18_7_19_1_12150 39 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 49 229 (accept_3_3 38 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 49 229 (Polychromatic418967fa.accept_13_11_10_8_1_1804 37 49 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 229 (accept_3_3 35 49 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 229
  (Polychromatic418967fa.accept_19_15_11_1_1_12437 34 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 229 (Polychromatic418967fa.accept_13_7_10_8_1_567 33 49 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 229 (accept_3_3 32 49 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 229 (Polychromatic418967fa.accept_13_5_10_8_1_1127 31 49 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 229
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 30 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 229 (accept_3_3 29 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 229 (Polychromatic418967fa.accept_17_10_15_8_1_6324 27 49 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 229 (accept_3_3 26 49 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 229 (Polychromatic418967fa.accept_13_12_10_8_1_3343 25 49
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 229
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 229 (accept_3_3 23 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 229 (Polychromatic418967fa.accept_16_6_1_5_1_2242 22 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 229 (Polychromatic418967fa.accept_24_21_1_13_1_6707 21 49 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 229 (accept_3_3 20 49 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 229 (Polychromatic418967fa.accept_23_19_3_22_1_13660 19 49
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 229
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 229 (accept_3_3 17 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 229 (Polychromatic418967fa.accept_14_2_7_5_1_5450 16 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 229 (Polychromatic418967fa.accept_13_2_10_8_1_1126 15 49 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 229 (accept_3_3 14 49 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 229 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 49
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 229 (accept_3_3 11 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 229 (Polychromatic418967fa.accept_17_10_15_8_1_6324 10 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 229 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 49 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 229 (accept_3_3 8 49 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 49 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 229
  (Polychromatic418967fa.accept_16_6_1_5_1_2242 6 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 229 (accept_3_3 5 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  229 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 49 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 229 (Polychromatic418967fa.accept_19_3_11_1_1_8319 3 49 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 229 (accept_3_3 2 49 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 229 (Polychromatic418967fa.accept_21_1_7_19_1_9193 1 49 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 229))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 229 (allA_succ_of_accept 47 48 229 (accept_3_3 47 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 48 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 229 (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 48
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 229 (accept_3_3 44 48 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 43
  48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 229 (accept_3_3 41 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  48 229 (Polychromatic418967fa.accept_13_1_9_8_1_1734 40 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 229 (accept_3_3 38 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 48 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 229 (accept_3_3 35 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 229 (accept_3_3 32 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 48 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 229
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 30 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 229 (accept_3_3 29 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 229 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 229 (accept_3_3 26 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 229 (accept_3_3 23 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 229 (accept_3_3 20 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 229 (accept_3_3 17 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 229 (accept_3_3 14 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 48 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 229
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 229 (accept_3_3 11 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 229 (Polychromatic418967fa.accept_19_9_10_1_1_8329 9 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 229 (accept_3_3 8 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 229 (accept_3_3 5 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 48 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 229 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 48 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 229 (accept_3_3 2 48 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 229)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 229 (allA_of_3_1 47 47 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 229 (allA_succ_of_accept 45 46
  229 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 229 (accept_3_3 44 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 229 (accept_3_3 41 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 46 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 229 (accept_3_3 38 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 229 (accept_3_3 35 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 46 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 229 (accept_3_3 32 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 229 (accept_3_3 29 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 46 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 229 (accept_3_3 26 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 229 (accept_3_3 23 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 46 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 229 (accept_3_3 20 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 229 (accept_3_3 17 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 46 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 229 (accept_3_3 14 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 229 (accept_3_3 11 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 229 (Polychromatic418967fa.accept_13_10_7_8_1_1794 10 46 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 229 (accept_3_3 8 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 46 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 229 (accept_3_3 5 46 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 229 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 46 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 229 (accept_3_3 2 46 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 46
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  229)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 229 (allA_succ_of_accept 44 45 229 (accept_3_3 44 45
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 229 (Polychromatic418967fa.accept_7_1_3_5_1_33
  43 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 229
  (Polychromatic418967fa.accept_16_10_13_5_1_3292 42 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 229 (accept_3_3 41 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  45 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 45 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 229 (accept_3_3 38 45 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 45 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 229 (accept_3_3 35 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 229 (Polychromatic418967fa.accept_16_1_13_5_1_2280 33 45 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 229 (accept_3_3 32 45 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 45 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 229 (accept_3_3 29 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 45 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 229 (accept_3_3 26 45 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 229 (Polychromatic418967fa.accept_16_9_13_5_1_2238 25 45 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 229
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 229 (accept_3_3 23 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 45 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 229 (accept_3_3 20 45 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 229 (Polychromatic418967fa.accept_17_2_11_8_1_2726 19 45 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 229
  (Polychromatic418967fa.accept_16_2_13_5_1_2257 18 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 229 (accept_3_3 17 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 45 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 229 (accept_3_3 14 45 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 229 (Polychromatic418967fa.accept_19_13_7_1_1_5379 13 45 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 229
  (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 229 (accept_3_3 11 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 229 (accept_3_3 8 45 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 229 (Polychromatic418967fa.accept_20_7_5_9_1_10833 7 45 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 229
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 229 (accept_3_3 5 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 45 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 229 (accept_3_3 2 45 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 45 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 229))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  229 (allA_of_3_1 44 44 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 229 (allA_succ_of_accept 42 43 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 229 (accept_3_3 41 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 229 (Polychromatic418967fa.accept_15_10_13_4_1_1210 40 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 229 (accept_3_3 38 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 43 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 229
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 229 (accept_3_3 35 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 229 (accept_3_3 32 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 229 (accept_3_3 29 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 229 (accept_3_3 26 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 43 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 229 (accept_3_3 23 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 229 (accept_3_3 20 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 43 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 229 (accept_3_3 17 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 229 (accept_3_3 14 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 43 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 229 (accept_3_3 11 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 229 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 229 (accept_3_3 8 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 229 (Polychromatic418967fa.accept_16_7_11_5_1_4402 7 43 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 229 (accept_3_3 5 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 43 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 43 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 229 (accept_3_3 2 43 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 229))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 229
  (allA_succ_of_accept 41 42 229 (accept_3_3 41 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 229 (Polychromatic418967fa.accept_22_18_20_9_1_13659 40 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 229 (accept_3_3 38 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 229
  (Polychromatic418967fa.accept_19_17_4_1_1_2763 36 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 229 (accept_3_3 35 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 229 (Polychromatic418967fa.accept_13_7_3_8_1_1750 33 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 229 (accept_3_3 32 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 229 (accept_3_3 29 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 229 (accept_3_3 26 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 42 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 229
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 229 (accept_3_3 23 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 229 (Polychromatic418967fa.accept_13_9_3_8_1_573 22 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 229 (accept_3_3 20 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 229
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 229 (accept_3_3 17 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 229 (accept_3_3 14 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 229 (Polychromatic418967fa.accept_16_13_10_5_1_2278 13 42 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 229 (accept_3_3 11 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 229 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 229 (accept_3_3 8 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 229
  (Polychromatic418967fa.accept_22_6_20_9_1_9031 6 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 229 (accept_3_3 5 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  229 (Polychromatic418967fa.accept_20_4_2_9_1_1261 4 42 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 42 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 229 (accept_3_3 2 42 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 229))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 41 229 (allA_of_3_1 41 41 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 229
  (allA_succ_of_accept 39 40 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 40 229 (accept_3_3 38 40 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 40 229 (Polychromatic418967fa.accept_13_11_1_8_1_1776 37 40 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 40 229
  (Polychromatic418967fa.accept_15_6_10_4_1_150 36 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 40 229 (accept_3_3 35 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  40 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 40 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 229 (accept_3_3 32 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 40 229 (Polychromatic418967fa.accept_13_5_1_8_1_1115 31 40 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 40 229
  (Polychromatic418967fa.accept_22_8_18_9_1_5631 30 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 40 229 (accept_3_3 29 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  40 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 40 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 229 (accept_3_3 26 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 40 229 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 40 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 40 229
  (Polychromatic418967fa.accept_11_2_7_9_1_890 24 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 40 229 (accept_3_3 23 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  40 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 40 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 40 229 (accept_3_3 20 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 40 229 (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 40 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 229
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 40 229 (accept_3_3 17 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  40 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 40 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 40 229 (accept_3_3 14 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 229 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 40 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 229
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 229 (accept_3_3 11 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  40 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 40 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 229 (accept_3_3 8 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 229 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 40 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 229
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 6 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 40 229 (accept_3_3 5 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 40
  229 (Polychromatic418967fa.accept_16_4_8_5_1_3317 4 40 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 40 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 229 (accept_3_3 2 40 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 229 (Polychromatic418967fa.accept_23_1_17_22_1_5357 1 40 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 229))))))))))))))))))))))))))))))))))))))))
  (allB_succ 39 229 (allA_succ_of_accept 38 39 229 (accept_3_3 38 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 39 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 229 (accept_3_3 35 39 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34
  39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 229 (accept_3_3 32 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 229 (Polychromatic418967fa.accept_24_7_15_13_1_8570 31 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 229 (accept_3_3 29 39 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 229 (accept_3_3 26 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 229 (accept_3_3 23 39 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 229 (accept_3_3 20 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 229 (accept_3_3 17 39 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 229 (accept_3_3 14 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 229 (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 39 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 229 (accept_3_3 11 39 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 229 (accept_3_3 8 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 229 (accept_3_3 5 39 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 229 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3
  39 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 229 (accept_3_3 2 39 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 39
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  229))))))))))))))))))))))))))))))))))))))) (allB_succ 38 229 (allA_of_3_1 38 38 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 229 (allA_succ_of_accept 36 37 229 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 37 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 229 (accept_3_3 35 37 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 34
  37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 229 (accept_3_3 32 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 229 (accept_3_3 29 37 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 229 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 37 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 229
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 229 (accept_3_3 26 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 229 (accept_3_3 23 37 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 229 (Polychromatic418967fa.accept_10_2_7_9_1_783 22 37 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 229 (accept_3_3 20 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 229 (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 37 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 229 (accept_3_3 17 37 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 229 (accept_3_3 14 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 37 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 229 (accept_3_3 11 37 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 37 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 229
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 229 (accept_3_3 8 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 37 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 229 (accept_3_3 5 37 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 37 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 229 (accept_3_3 2 37 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 229 (Polychromatic418967fa.accept_13_1_11_8_1_2562
  1 37 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  229))))))))))))))))))))))))))))))))))))) (allB_succ 36 229 (allA_succ_of_accept 35 36 229 (accept_3_3 35 36 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 34
  36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 229
  (Polychromatic418967fa.accept_8_1_4_5_1_48 33 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 36 229 (accept_3_3 32 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  36 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 36 229 (Polychromatic418967fa.accept_13_4_10_8_1_1817 30 36 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 229 (accept_3_3 29 36 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 28 36 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 36 229 (accept_3_3 26 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  36 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 36 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 36 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 229 (accept_3_3 23 36 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 229 (Polychromatic418967fa.accept_16_6_4_5_1_2272 22 36 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 229
  (Polychromatic418967fa.accept_25_21_11_4_1_13658 21 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 229 (accept_3_3 20 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 36 229 (Polychromatic418967fa.accept_20_19_16_9_1_9433 19 36 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 36 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 229 (accept_3_3 17 36 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 229 (Polychromatic418967fa.accept_17_16_2_8_1_7625
  16 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 229
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 36 229 (accept_3_3 14 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  36 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 36 229 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 36 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 229 (accept_3_3 11 36 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 36 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 36 229
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 36 229 (accept_3_3 8 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36
  229 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 36 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 36 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 229 (accept_3_3 5 36 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 36 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 229 (accept_3_3 2 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36
  229 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 229)))))))))))))))))))))))))))))))))))) (allB_succ 35 229 (allA_of_3_1 35 35 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 229 (allA_succ_of_accept 33 34 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 229 (accept_3_3 32 34 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 34 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  34 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 34 229 (accept_3_3 29 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  34 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 34 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 229 (accept_3_3 26 34 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 34 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 34 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 34 229 (accept_3_3 23 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  34 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 34 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 34 229 (accept_3_3 20 34 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 34 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 34 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 34 229 (accept_3_3 17 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  34 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 34 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 34 229 (accept_3_3 14 34 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 34 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 34 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 34 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 34 229 (accept_3_3 11 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  34 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 34 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 34 229 (accept_3_3 8 34 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 34 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 34 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 34 229 (accept_3_3 5 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 34
  229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 34 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 34 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 229 (accept_3_3 2 34 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 34 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 34 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 229)))))))))))))))))))))))))))))))))) (allB_succ 33 229
  (allA_succ_of_accept 32 33 229 (accept_3_3 32 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  33 229 (Polychromatic418967fa.accept_15_1_3_4_1_1217 31 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 33 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 33 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 229 (accept_3_3 29 33 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 229 (accept_3_3 26 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 33 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 229 (accept_3_3 23 33 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 33 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 229 (accept_3_3 20 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 229 (Polychromatic418967fa.accept_19_18_14_1_1_8323 18 33 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 229 (accept_3_3 17 33 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 229 (accept_3_3 14 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 229 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 229 (accept_3_3 11 33 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 229
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 229 (accept_3_3 8 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 33 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 33 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 229 (accept_3_3 5 33 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  33 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 229 (accept_3_3 2 33 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 33
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 229)))))))))))))))))))))))))))))))))
  (allB_succ 32 229 (allA_of_3_1 32 32 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 229
  (allA_succ_of_accept 30 31 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 229 (accept_3_3 29 31 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 28 31 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 229 (Polychromatic418967fa.accept_13_1_5_8_1_207
  27 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 229 (accept_3_3 26
  31 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 229
  (Polychromatic418967fa.accept_10_5_1_9_1_791 25 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 229 (Polychromatic418967fa.accept_17_7_14_8_1_5069 24 31 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 229 (accept_3_3 23 31 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 229 (Polychromatic418967fa.accept_19_2_12_1_1_2815
  21 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 229 (accept_3_3 20
  31 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 229
  (Polychromatic418967fa.accept_24_19_7_13_1_10414 19 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 229 (accept_3_3 17 31 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 31 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 229 (accept_3_3 14 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 229 (Polychromatic418967fa.accept_19_13_12_1_1_3993 13 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 31 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 229 (accept_3_3 11 31 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 229 (accept_3_3 8 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  229 (Polychromatic418967fa.accept_17_7_14_8_1_5069 7 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 31 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 229 (accept_3_3 5 31 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 229 (Polychromatic418967fa.accept_16_4_15_5_1_5537 4 31 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 229
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 229 (accept_3_3 2 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31
  229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 31 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 229))))))))))))))))))))))))))))))) (allB_succ 30 229 (allA_succ_of_accept 29 30 229 (accept_3_3 29 30 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 28
  30 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 30 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 30 229 (accept_3_3 26 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  30 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 30 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 30 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 229 (accept_3_3 23 30 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 229 (Polychromatic418967fa.accept_13_9_4_8_1_1752 22 30 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 30 229
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 30 229 (accept_3_3 20 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  30 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 30 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 30 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 229 (accept_3_3 17 30 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 30 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 30 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 30 229 (accept_3_3 14 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  30 229 (Polychromatic418967fa.accept_20_13_10_9_1_5030 13 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 30 229 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 30 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 229 (accept_3_3 11 30 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 30 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 229
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 229 (accept_3_3 8 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30
  229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 30 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 30 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 229 (accept_3_3 5 30 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 30 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 30 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 229 (accept_3_3 2 30 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 30
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 229))))))))))))))))))))))))))))))
  (allB_succ 29 229 (allA_of_3_1 29 29 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 229
  (allA_succ_of_accept 27 28 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 229 (accept_3_3 26 28 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 28 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 24
  28 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 229 (accept_3_3 23 28
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 229
  (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 28 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 28 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 229 (accept_3_3 20 28 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 28 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 28 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 229 (Polychromatic418967fa.accept_17_1_11_8_1_2725
  18 28 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 229 (accept_3_3 17
  28 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 229
  (Polychromatic418967fa.accept_9_7_1_4_1_217 16 28 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 28 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 229 (accept_3_3 14 28 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 28 229 (Polychromatic418967fa.accept_21_13_7_19_1_4505 13 28 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 28 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 229 (accept_3_3 11 28 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 28 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 229 (accept_3_3 8 28 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 28 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 229 (accept_3_3 5 28 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  229 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 28 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 28 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 229 (accept_3_3 2 28 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 28 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 28 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 229)))))))))))))))))))))))))))) (allB_succ 27 229
  (allA_succ_of_accept 26 27 229 (accept_3_3 26 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  27 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 27 229 (Polychromatic418967fa.accept_13_11_1_8_1_1776 24 27 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 229 (accept_3_3 23 27 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 229 (accept_3_3 20 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 229 (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 229 (accept_3_3 17 27 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 229 (accept_3_3 14 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 229 (Polychromatic418967fa.accept_19_13_8_1_1_8290 13 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 229 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 27 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 229 (accept_3_3 11 27 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 229 (accept_3_3 8 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  229 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 229 (accept_3_3 5 27 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 229 (Polychromatic418967fa.accept_18_3_9_13_1_1235
  3 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 229 (accept_3_3 2 27
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 229 (Polychromatic418967fa.accept_7_1_6_5_1_39
  1 27 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 229)))))))))))))))))))))))))))
  (allB_succ 26 229 (allA_of_3_1 26 26 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 229
  (allA_succ_of_accept 24 25 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 25 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 229 (accept_3_3 23 25 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 25 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 21
  25 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 229 (accept_3_3 20 25
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 229 (Polychromatic418967fa.accept_9_1_7_4_1_52
  19 25 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 229
  (Polychromatic418967fa.accept_13_5_12_8_1_198 18 25 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 229 (accept_3_3 17 25 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 25 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 25 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 229 (accept_3_3 14 25 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 25 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 229 (accept_3_3 11 25 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 25 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 25 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 229 (accept_3_3 8 25 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 229 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 25 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 25 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 229 (accept_3_3 5 25 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  229 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 25 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 25 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 229 (accept_3_3 2 25 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 229))))))))))))))))))))))))) (allB_succ 24 229
  (allA_succ_of_accept 23 24 229 (accept_3_3 23 24 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  24 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 24 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 24 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 229 (accept_3_3 20 24 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 24 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 229
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 24 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 229 (accept_3_3 17 24 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 24 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 229 (accept_3_3 14 24 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 24 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 24 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 229 (accept_3_3 11 24 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 24 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 229 (accept_3_3 8 24 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 229
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 6 24 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 229 (accept_3_3 5 24 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  229 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 24 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 229 (accept_3_3 2 24 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 229)))))))))))))))))))))))) (allB_succ 23 229 (allA_of_3_1 23 23
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 229 (allA_succ_of_accept 21 22 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 229 (accept_3_3 20 22 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 22 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 229 (accept_3_3 17 22 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 22 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 229 (accept_3_3 14 22 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 22 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 229 (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 22 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 229 (accept_3_3 11 22 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 22 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 229 (accept_3_3 8 22 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 22 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 229 (accept_3_3 5 22 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 22 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 229 (accept_3_3 2 22 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 1
  22 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 229)))))))))))))))))))))) (allB_succ
  21 229 (allA_succ_of_accept 20 21 229 (accept_3_3 20 21 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 21 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 21 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 229 (accept_3_3 17 21 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  21 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 229 (accept_3_3 14 21 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 229 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 21 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 21 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 229 (accept_3_3 11 21 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 21 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 229
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 21 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 229 (accept_3_3 8 21 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 21 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 229 (accept_3_3 5 21 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  21 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 229 (accept_3_3 2 21 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 21
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 229))))))))))))))))))))) (allB_succ 20
  229 (allA_of_3_1 20 20 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 229 (allA_succ_of_accept 18 19 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 229 (accept_3_3 17 19 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 19 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 19 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 229 (accept_3_3 14 19 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 229 (Polychromatic418967fa.accept_20_13_19_9_1_10976 13 19 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 229 (accept_3_3 11 19 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 229 (Polychromatic418967fa.accept_23_9_19_22_1_13657 9 19 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 229 (accept_3_3 8 19 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 229 (accept_3_3 5 19 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  229 (Polychromatic418967fa.accept_20_4_19_9_1_7961 4 19 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 19 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 229 (accept_3_3 2 19 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 229 (Polychromatic418967fa.accept_13_1_6_8_1_208 1 19 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 229))))))))))))))))))) (allB_succ 18 229
  (allA_succ_of_accept 17 18 229 (accept_3_3 17 18 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  18 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 18 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 18 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 229 (accept_3_3 14 18 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 18 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 229
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 18 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 18 229 (accept_3_3 11 18 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  18 229 (Polychromatic418967fa.accept_13_10_5_8_1_2555 10 18 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 18 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 229 (accept_3_3 8 18 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 18 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 229 (accept_3_3 5 18 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18
  229 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 18 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 18 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 229 (accept_3_3 2 18 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 18 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 18 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 229)))))))))))))))))) (allB_succ 17 229 (allA_of_3_1 17 17 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 229 (allA_succ_of_accept 15 16 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 229 (accept_3_3 14 16 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 16 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 16 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 229 (accept_3_3 11 16 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 16 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 229 (accept_3_3 8 16 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  229 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 16 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 16 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 229 (accept_3_3 5 16 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 16 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 229 (accept_3_3 2 16 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 16
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 229)))))))))))))))) (allB_succ 15 229
  (allA_succ_of_accept 14 15 229 (accept_3_3 14 15 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  15 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 15 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 15 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 229 (accept_3_3 11 15 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 15 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 229 (accept_3_3 8 15 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 15 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 229 (accept_3_3 5 15 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 15 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 229 (accept_3_3 2 15 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 15
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 229))))))))))))))) (allB_succ 14 229
  (allA_of_3_1 14 14 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 229 (allA_succ_of_accept 12 13 229
  (Polychromatic418967fa.accept_19_12_13_1_1_2779 12 13 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 229 (accept_3_3 11 13 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 229 (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 13 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 229 (Polychromatic418967fa.accept_15_9_13_4_1_1209 9 13 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 229 (accept_3_3 8 13 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 13 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 229
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 13 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 229 (accept_3_3 5 13 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 13 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 229 (Polychromatic418967fa.accept_17_3_13_8_1_11337 3 13 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 229 (accept_3_3 2 13 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 229))))))))))))) (allB_succ 12 229 (allA_succ_of_accept 11 12
  229 (accept_3_3 11 12 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 229
  (Polychromatic418967fa.accept_9_1_3_4_1_47 10 12 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 12 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 229 (accept_3_3 8 12 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 6
  12 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 229 (accept_3_3 5 12 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 229 (Polychromatic418967fa.accept_13_4_12_8_1_197 4
  12 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 229
  (Polychromatic418967fa.accept_14_3_12_5_1_153 3 12 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 229 (accept_3_3 2 12 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  229 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 12 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 229)))))))))))) (allB_succ 11 229 (allA_of_3_1 11 11 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 229 (allA_succ_of_accept 9 10 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 229 (accept_3_3 8 10 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 10 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 229 (accept_3_3 5 10 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  229 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 10 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 10 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 229 (accept_3_3 2 10 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 10 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 229)))))))))) (allB_succ 9 229 (allA_succ_of_accept 8
  9 229 (accept_3_3 8 9 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 229
  (Polychromatic418967fa.accept_13_7_9_8_1_188 7 9 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 229 (Polychromatic418967fa.accept_15_6_9_4_1_1227 6 9 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 229 (accept_3_3 5 9 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 9
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 229 (accept_3_3 2 9 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 229 (Polychromatic418967fa.accept_13_1_9_8_1_1734 1
  9 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 229))))))))) (allB_succ 8 229
  (allA_of_3_1 8 8 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 229 (allA_succ_of_accept 6 7 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 229 (accept_3_3 5 7 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 229
  (Polychromatic418967fa.accept_17_4_7_8_1_7491 4 7 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 7 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 229 (accept_3_3 2 7 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 229))))))) (allB_succ 6 229 (allA_succ_of_accept 5 6 229
  (accept_3_3 5 6 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 6 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 229 (accept_3_3 2 6 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 6 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 229)))))) (allB_succ 5 229 (allA_of_3_1 5 5 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 229 (allA_succ_of_accept 3 4 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 229 (accept_3_3 2 4 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 4 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 229)))) (allB_succ 3 229 (allA_succ_of_accept 2 3 229 (accept_3_3 2 3 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 3 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 229))) (allB_succ 2 229 (allA_of_3_1 2 2 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


