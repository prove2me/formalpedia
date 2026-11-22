-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch257_Segment000
-- name    : Polychromatic418967fa_Branch257_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:31.51018+00:00
-- url     : https://prove2.me/theorems/92f4c22a-c3d0-4360-b660-7ecc7e9bc613
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

def Polychromatic418967fa.branch_257_segment_000 : allB 123 257 :=
  allB_succ 122 257 (allA_succ_of_accept 121 122 257 (accept_3_2 121 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 122 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 120 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 119 122
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 122 257 (accept_3_2 118 122
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 122 257
  (Polychromatic418967fa.accept_6_3_2_5_1_32 117 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 122 257 (Polychromatic418967fa.accept_12_8_2_5_1_844 116 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 122 257 (accept_3_2 115 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 122 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 114 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 122 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 113 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 122 257 (accept_3_2 112 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 122 257 (Polychromatic418967fa.accept_13_6_5_10_1_1213 110 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 122 257 (accept_3_2 109 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 122 257 (Polychromatic418967fa.accept_13_4_5_10_1_1247 108
  122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 122 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 107 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 122 257 (accept_3_2 106 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 122 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 122 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 104 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 122 257 (accept_3_2 103 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 122 257 (Polychromatic418967fa.accept_22_14_12_15_1_11098 102
  122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 122 257
  (Polychromatic418967fa.accept_18_11_14_5_1_3951 101 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 122 257 (accept_3_2 100 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 122 257 (Polychromatic418967fa.accept_18_8_14_5_1_2778 98 122
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 122 257 (accept_3_2 97 122
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 122 257
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 96 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 122 257 (accept_3_2 94 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 122 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 122 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 92
  122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 122 257 (accept_3_2 91
  122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 122 257
  (Polychromatic418967fa.accept_17_5_3_2_1_5847 90 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 122 257 (Polychromatic418967fa.accept_10_9_2_7_1_1096 89 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 122 257 (accept_3_2 88 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 122 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 86
  122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 122 257 (accept_3_2 85
  122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 122 257
  (Polychromatic418967fa.accept_10_4_2_7_1_373 84 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 122 257 (accept_3_2 82 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 122 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 122 257 (Polychromatic418967fa.accept_12_8_2_5_1_844
  80 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 122 257 (accept_3_2 79
  122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 122 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 78 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 122 257 (Polychromatic418967fa.accept_21_14_17_5_1_3459 77 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 122 257 (accept_3_2 76 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 122 257
  (Polychromatic418967fa.accept_10_4_2_7_1_373 74 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 122 257 (accept_3_2 73 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 122 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 122 257 (accept_3_2 70 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 122 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 122 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 122 257 (accept_3_2 67 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 122 257 (Polychromatic418967fa.accept_23_20_7_4_1_15680 66 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 122 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 122 257 (accept_3_2 64 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 122 257
  (Polychromatic418967fa.accept_17_11_3_2_1_5867 62 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 122 257 (accept_3_2 61 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 122 257 (Polychromatic418967fa.accept_13_8_5_10_1_2701 60 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 122 257 (accept_3_2 58 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 122 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 122 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 122 257 (accept_3_2 55 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 122 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 122 257 (Polychromatic418967fa.accept_21_11_17_5_1_8161 53 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 257 (accept_3_2 52 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 122 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 257 (accept_3_2 49 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 257 (Polychromatic418967fa.accept_17_14_3_2_1_5848 48 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 257 (accept_3_2 46 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 122 257 (accept_3_2 43 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 122 257 (Polychromatic418967fa.accept_19_4_8_10_1_11682 42 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 122 257 (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 257 (accept_3_2 40 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 122 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 257
  (Polychromatic418967fa.accept_20_18_2_17_1_14188 38 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 122 257 (accept_3_2 37 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 122 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 122 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 257 (accept_3_2 34 122 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 257 (accept_3_2 31 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 257 (accept_3_2 28 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 257
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 26 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 122 257 (accept_3_2 25 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 122 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 122 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 257 (accept_3_2 22 122 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 257 (accept_3_2 19 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 257 (Polychromatic418967fa.accept_17_1_3_2_1_5846 18 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 257 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 257 (accept_3_2 16 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 257
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 257 (accept_3_2 13 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 257 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 257 (accept_3_2 10 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 257 (accept_3_2 7 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 257 (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 257 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 257 (accept_3_2 4 122 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 257 (accept_3_2 1 122 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 257 (allA_of_3_0 121 121 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 257
  (allA_succ_of_accept 119 120 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 119 120 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 120 257 (accept_3_2 118 120 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 120 257 (Polychromatic418967fa.accept_18_9_12_5_1_864 117 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 116 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 120 257 (accept_3_2 115 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 120 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 114 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 120 257 (Polychromatic418967fa.accept_21_8_15_5_1_8178 113 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 120 257 (accept_3_2 112 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 111 120
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 120 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 110 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 120 257 (accept_3_2 109 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 120 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 108 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 120 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 107 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 257 (accept_3_2 106 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 120 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 120
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 120 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 104 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 120 257 (accept_3_2 103 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 120 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 102 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 120 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 101 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 257 (accept_3_2 100 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 257 (Polychromatic418967fa.accept_18_9_12_5_1_864 99 120
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 120 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 98 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 120 257 (accept_3_2 97 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 120 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 120 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 95 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 257 (accept_3_2 94 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 257 (Polychromatic418967fa.accept_11_5_10_4_1_1157 93 120 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 92 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 120 257 (accept_3_2 91 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 120 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 120 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 89 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 257 (accept_3_2 88 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 257
  (Polychromatic418967fa.accept_26_8_16_23_1_15679 86 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 120 257 (accept_3_2 85 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 120 257 (Polychromatic418967fa.accept_13_6_3_10_1_698 84 120 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 120 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 83 120 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 257 (accept_3_2 82 120 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 257 (Polychromatic418967fa.accept_7_4_1_5_1_540
  81 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 120 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 80 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 120 257 (accept_3_2 79 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 120 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 120 257 (Polychromatic418967fa.accept_19_1_6_10_1_3366 77 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 257 (accept_3_2 76 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 257 (Polychromatic418967fa.accept_21_12_15_5_1_12686 75
  120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 120 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 120 257 (accept_3_2 73 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 120 257 (Polychromatic418967fa.accept_13_7_3_10_1_656 72 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 120 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 257 (accept_3_2 70 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 120 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 257
  (Polychromatic418967fa.accept_16_4_8_1_1_5257 68 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 120 257 (accept_3_2 67 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 120 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 120 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 257 (accept_3_2 64 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 257 (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 120 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 257 (accept_3_2 61 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 120 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 120 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 257 (accept_3_2 58 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 257 (Polychromatic418967fa.accept_16_9_8_1_1_1228 57 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 120 257 (accept_3_2 55 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 120 257 (Polychromatic418967fa.accept_13_2_3_10_1_658 54 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 120 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 257 (accept_3_2 52 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 257
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 50 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 120 257 (accept_3_2 49 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 120 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 120 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 120 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 257 (accept_3_2 46 120 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 45
  120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 257 (accept_3_2 43 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 120 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 120 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 257 (accept_3_2 40 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 257 (accept_3_2 37 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 120 257 (Polychromatic418967fa.accept_16_4_8_1_1_5257 36 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 120 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 257 (accept_3_2 34 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 257 (accept_3_2 31 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 120 257 (Polychromatic418967fa.accept_17_13_1_2_1_9714 30 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 120 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 257 (accept_3_2 28 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 120 257 (accept_3_2 25 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 120 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 120 257 (Polychromatic418967fa.accept_16_7_8_1_1_3061 23 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 257 (accept_3_2 22 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 257 (Polychromatic418967fa.accept_19_2_6_10_1_3364 21 120
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 257 (accept_3_2 19 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 257 (accept_3_2 16 120 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 257
  (Polychromatic418967fa.accept_19_14_6_10_1_11678 14 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 120 257 (accept_3_2 13 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 120 257 (Polychromatic418967fa.accept_16_12_8_1_1_5270 12 120 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 120 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 257 (accept_3_2 10 120 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 257 (Polychromatic418967fa.accept_16_9_8_1_1_1228
  9 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 257 (accept_3_2 7 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 120 257 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 257 (accept_3_2 4 120 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 257 (accept_3_2 1 120 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 257 (allA_succ_of_accept 118 119 257 (accept_3_2 118 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 257 (Polychromatic418967fa.accept_15_12_14_2_1_3794 117 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 257 (Polychromatic418967fa.accept_9_8_2_5_1_237
  116 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 257 (accept_3_2
  115 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 114 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 257 (Polychromatic418967fa.accept_19_18_5_10_1_2175 113 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 257 (accept_3_2 112 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 119 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 111 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 110 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 119 257 (accept_3_2 109 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 119 257 (Polychromatic418967fa.accept_10_8_9_7_1_1118 108 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 119 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 107 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 257 (accept_3_2 106 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 105 119
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 257
  (Polychromatic418967fa.accept_16_8_7_1_1_8875 104 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 119 257 (accept_3_2 103 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 119 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 119 257 (Polychromatic418967fa.accept_11_2_9_4_1_310 101 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 257 (accept_3_2 100 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 257 (Polychromatic418967fa.accept_13_8_2_10_1_652 99 119
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 98 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 119 257 (accept_3_2 97 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 119 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 96 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 119 257 (Polychromatic418967fa.accept_15_5_14_2_1_1876 95 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 257 (accept_3_2 94 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 93 119 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 257
  (Polychromatic418967fa.accept_10_2_9_7_1_720 92 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 257 (accept_3_2 91 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 257 (accept_3_2 88 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 87 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 257 (accept_3_2 85 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 257 (Polychromatic418967fa.accept_13_5_2_10_1_248 83 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 257 (accept_3_2 82 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 257 (Polychromatic418967fa.accept_13_3_2_10_1_2697 81 119
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 80 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 257 (accept_3_2 79 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 119 257 (Polychromatic418967fa.accept_13_12_2_10_1_2698 77 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 257 (accept_3_2 76 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 119 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 257 (accept_3_2 73 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 257 (accept_3_2 70 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 257
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 68 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 257 (accept_3_2 67 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 257 (Polychromatic418967fa.accept_14_9_7_5_1_1105 65 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 257 (accept_3_2 64 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 257 (Polychromatic418967fa.accept_13_11_2_10_1_4399 63 119
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 257 (accept_3_2 61 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 257 (Polychromatic418967fa.accept_19_2_5_10_1_4608 59 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 257 (accept_3_2 58 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 119 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 257
  (Polychromatic418967fa.accept_16_8_7_1_1_8875 56 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 257 (accept_3_2 55 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 257 (accept_3_2 52 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 257 (accept_3_2 49 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 257 (Polychromatic418967fa.accept_13_8_2_10_1_652 47 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 257 (accept_3_2 46 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 257 (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 119
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 257 (accept_3_2 43 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 257 (Polychromatic418967fa.accept_19_3_5_10_1_6033 41 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 257 (accept_3_2 40 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 119 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 257 (accept_3_2 37 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 257 (Polychromatic418967fa.accept_20_16_19_17_1_723 36 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 257 (accept_3_2 34 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 257
  (Polychromatic418967fa.accept_10_2_9_7_1_720 32 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 257 (accept_3_2 31 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 257 (Polychromatic418967fa.accept_13_3_2_10_1_2697 29 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 257 (accept_3_2 28 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 257 (Polychromatic418967fa.accept_15_12_14_2_1_3794 27 119
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 257 (accept_3_2 25 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 257 (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 257 (accept_3_2 22 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 119 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 257
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 257 (accept_3_2 19 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 257 (accept_3_2 16 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 257 (accept_3_2 13 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 257 (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 257 (accept_3_2 10 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 257 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 119 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 257 (accept_3_2 7 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 257 (Polychromatic418967fa.accept_13_5_2_10_1_248 5 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 257 (accept_3_2 4 119 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 119 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 257 (accept_3_2 1 119 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 257 (allA_of_3_0 118 118 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 257
  (allA_succ_of_accept 116 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 117 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 257 (accept_3_2 115 117 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 117 257 (Polychromatic418967fa.accept_21_9_12_5_1_317 114 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 257
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 113 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 257 (accept_3_2 112 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 111 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 257 (accept_3_2 109 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 108 117
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 257
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 107 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 257 (accept_3_2 106 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 257 (Polychromatic418967fa.accept_16_9_5_1_1_1259 105 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 257 (accept_3_2 103 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 257 (Polychromatic418967fa.accept_11_3_7_4_1_1133 102 117
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 257
  (Polychromatic418967fa.accept_21_17_12_5_1_15677 101 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 117 257 (accept_3_2 100 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 117 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 99 117 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 257 (accept_3_2 97 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 257 (Polychromatic418967fa.accept_11_8_7_4_1_3011
  96 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 257
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 95 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 257 (accept_3_2 94 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 117 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 93 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 257 (accept_3_2 91 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 257 (Polychromatic418967fa.accept_21_6_12_5_1_6593 90 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 257
  (Polychromatic418967fa.accept_15_14_12_2_1_3804 89 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 117 257 (accept_3_2 88 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 117 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 87 117 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 257 (accept_3_2 85 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 257 (Polychromatic418967fa.accept_8_4_5_1_1_299
  84 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 257
  (Polychromatic418967fa.accept_19_7_3_10_1_4674 83 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 117 257 (accept_3_2 82 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 117 257 (Polychromatic418967fa.accept_15_6_12_2_1_2803 81 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 257 (accept_3_2 79 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 78 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 257
  (Polychromatic418967fa.accept_16_13_5_1_1_3017 77 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 257 (accept_3_2 76 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 117 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 257 (accept_3_2 73 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 257 (Polychromatic418967fa.accept_17_4_15_2_1_4551 72 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 257
  (Polychromatic418967fa.accept_21_8_12_5_1_8209 71 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 257 (accept_3_2 70 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 117 257 (Polychromatic418967fa.accept_11_3_7_4_1_1133 69 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 257 (accept_3_2 67 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 257 (Polychromatic418967fa.accept_15_6_12_2_1_2803 66 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 257
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 65 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 257 (accept_3_2 64 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 257 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 257 (accept_3_2 61 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 257
  (Polychromatic418967fa.accept_15_14_12_2_1_3804 59 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 117 257 (accept_3_2 58 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 117 257 (Polychromatic418967fa.accept_16_9_5_1_1_1259 57 117 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 257 (accept_3_2 55 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 257 (Polychromatic418967fa.accept_16_6_5_1_1_7761
  54 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 257
  (Polychromatic418967fa.accept_19_15_3_10_1_10389 53 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 117 257 (accept_3_2 52 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 117 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 117 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 257 (accept_3_2 49 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 257 (Polychromatic418967fa.accept_15_3_12_2_1_507
  48 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 257
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 47 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 257 (accept_3_2 46 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 257 (Polychromatic418967fa.accept_16_13_5_1_1_3017 45 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 257 (accept_3_2 43 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 257 (Polychromatic418967fa.accept_22_20_7_15_1_15678 42 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 257
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 41 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 257 (accept_3_2 40 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 257 (accept_3_2 37 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 257
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 257 (accept_3_2 34 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 257 (accept_3_2 31 117 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 257 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 257
  (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 117 257 (accept_3_2 28 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 117 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 117 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 257 (accept_3_2 25 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 257
  (Polychromatic418967fa.accept_17_7_15_2_1_10843 24 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 257 (Polychromatic418967fa.accept_27_23_9_14_1_9951 23 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 257 (accept_3_2 22 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 257 (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 117
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 257 (accept_3_2 19 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 257 (Polychromatic418967fa.accept_21_17_12_5_1_15677 17 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 257 (accept_3_2 16 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 117
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 257 (accept_3_2 13 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 257 (Polychromatic418967fa.accept_19_11_3_10_1_3354 11 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 257 (accept_3_2 10 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 257 (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 257 (accept_3_2 7 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 257 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 257 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 257 (accept_3_2 4 117 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 257 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 117 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 257 (accept_3_2 1 117 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 257 (allA_succ_of_accept 115 116 257 (accept_3_2 115 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 116 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 114 116 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 116 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 113 116
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 116 257 (accept_3_2 112 116
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 116 257
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 116 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 110 116 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 116 257 (accept_3_2 109 116 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 116 257 (Polychromatic418967fa.accept_16_12_4_1_1_1257 108 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 116 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 107 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 116 257 (accept_3_2 106 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 116 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 104 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 257 (accept_3_2 103 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 116 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 102 116
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 116 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 101 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 116 257 (accept_3_2 100 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 116 257 (Polychromatic418967fa.accept_12_2_8_5_1_408 98 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 116 257 (accept_3_2 97 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 116 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 116 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 116 257
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 95 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 116 257 (accept_3_2 94 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 116 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 92 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 116 257 (accept_3_2 91 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 116 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 90 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 116 257
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 89 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 116 257 (accept_3_2 88 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 116 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 116 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 86 116 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 116 257 (accept_3_2 85 116 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 116 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 84
  116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 116 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 83 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 116 257 (accept_3_2 82 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 116 257 (Polychromatic418967fa.accept_13_2_12_10_1_2649 80 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 116 257 (accept_3_2 79 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 116 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 116 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 77 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 116 257 (accept_3_2 76 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 116 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 116 257 (accept_3_2 73 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 116 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 116 257 (accept_3_2 70 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 116 257 (Polychromatic418967fa.accept_11_2_6_4_1_3028 68 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 257 (accept_3_2 67 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 116 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 65 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 257 (accept_3_2 64 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 62 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 257 (accept_3_2 61 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 257
  (Polychromatic418967fa.accept_13_7_12_10_1_640 59 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 257 (accept_3_2 58 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 257 (accept_3_2 55 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 257 (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 116 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 257 (accept_3_2 52 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 257 (accept_3_2 49 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 257 (accept_3_2 46 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 257 (accept_3_2 43 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 257 (accept_3_2 40 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 257 (accept_3_2 37 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 257
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 257 (accept_3_2 34 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 257 (Polychromatic418967fa.accept_13_6_12_10_1_690 32 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 257 (accept_3_2 31 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 116 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 257 (accept_3_2 28 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 257 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 257 (accept_3_2 25 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 116 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 257 (accept_3_2 22 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 257 (accept_3_2 19 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 257 (Polychromatic418967fa.accept_19_18_2_10_1_10412 18 116 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 257
  (Polychromatic418967fa.accept_18_17_8_5_1_2769 17 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 257 (accept_3_2 16 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 257 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 257 (accept_3_2 13 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 116 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 257 (accept_3_2 10 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 257 (accept_3_2 7 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 116 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 257 (accept_3_2 4 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 257 (accept_3_2 1 116 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 257 (allA_of_3_0 115 115 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 257
  (allA_succ_of_accept 113 114 257 (Polychromatic418967fa.accept_10_3_4_7_1_353 113 114 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 114 257 (accept_3_2 112 114 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 114 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 110 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 114 257 (accept_3_2 109 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 114 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 108 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 114 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 107 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 257 (accept_3_2 106 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 257 (Polychromatic418967fa.accept_14_7_2_5_1_4528 105 114
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 114 257
  (Polychromatic418967fa.accept_22_16_4_15_1_7881 104 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 114 257 (accept_3_2 103 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 114 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 102 114 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 101 114
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 257 (accept_3_2 100 114
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 99 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 114 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 98 114 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 114 257 (accept_3_2 97 114 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 114 257 (Polychromatic418967fa.accept_21_12_9_5_1_6547 96 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 114 257 (accept_3_2 94 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 114 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 114 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 114 257 (accept_3_2 91 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 114 257 (Polychromatic418967fa.accept_23_21_22_4_1_9119 90 114 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 114 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 89 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 114 257 (accept_3_2 88 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 114 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 114 257 (Polychromatic418967fa.accept_15_11_9_2_1_4780 86 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 114 257 (accept_3_2 85 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 114 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 114 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 114 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 114 257 (accept_3_2 82 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 114 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 114 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 80 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 257 (accept_3_2 79 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 114 257 (Polychromatic418967fa.accept_17_10_12_2_1_3385 78 114 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 114 257
  (Polychromatic418967fa.accept_14_7_2_5_1_4528 77 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 114 257 (accept_3_2 76 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 114 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 114 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 74 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 257 (accept_3_2 73 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 114 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 114 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 114 257 (accept_3_2 70 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 114 257 (Polychromatic418967fa.accept_18_15_6_5_1_3972 69 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 114 257 (Polychromatic418967fa.accept_15_8_9_2_1_1897 68 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 257 (accept_3_2 67 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 114 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 114 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 65 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 114 257 (accept_3_2 64 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 114 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 114 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 257 (accept_3_2 61 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 114 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 114 257 (accept_3_2 58 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 114 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 114 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 257 (accept_3_2 55 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 257 (Polychromatic418967fa.accept_16_6_2_1_1_4081 54 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 114 257 (accept_3_2 52 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 114 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 114 257 (Polychromatic418967fa.accept_26_24_10_23_1_13784 50 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 257 (accept_3_2 49 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 114 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 114 257 (accept_3_2 46 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 114 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 114 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 257 (accept_3_2 43 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 257
  (Polychromatic418967fa.accept_10_1_4_7_1_374 41 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 114 257 (accept_3_2 40 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 114 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 114 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 257 (accept_3_2 37 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 257 (Polychromatic418967fa.accept_21_15_9_5_1_6588 36 114 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 257 (accept_3_2 34 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 114 257 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 114 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 257 (accept_3_2 31 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 114 257 (accept_3_2 28 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 114 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 114 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 257 (accept_3_2 25 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 257 (accept_3_2 22 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 114 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 114 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 257 (accept_3_2 19 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 257 (accept_3_2 16 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 114 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 114 257 (Polychromatic418967fa.accept_21_14_9_5_1_6616 14 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 257 (accept_3_2 13 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 114 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 257 (accept_3_2 10 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  114 257 (Polychromatic418967fa.accept_16_9_2_1_1_3077 9 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 114 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 257 (accept_3_2 7 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 257 (Polychromatic418967fa.accept_16_6_2_1_1_4081 6 114 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 257
  (Polychromatic418967fa.accept_22_5_4_15_1_15676 5 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 257 (accept_3_2 4 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  114 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 114 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 257 (accept_3_2 1 114 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 114
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 257 (allA_succ_of_accept 112 113 257 (accept_3_2 112 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 111 113 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 257 (Polychromatic418967fa.accept_13_6_9_10_1_1201 110
  113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 257 (accept_3_2 109
  113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 108 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 257 (Polychromatic418967fa.accept_21_2_8_5_1_5057 107 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 257 (accept_3_2 106 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 113 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 105 113 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 104 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 257 (accept_3_2 103 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 102 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 101 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 257 (accept_3_2 100 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 257 (Polychromatic418967fa.accept_15_9_8_2_1_1109 99 113
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 257
  (Polychromatic418967fa.accept_21_14_8_5_1_6586 98 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 257 (accept_3_2 97 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 257 (Polychromatic418967fa.accept_10_6_3_7_1_2197 96 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 95 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 257 (accept_3_2 94 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 257 (Polychromatic418967fa.accept_17_8_11_2_1_3415 93 113 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 257
  (Polychromatic418967fa.accept_13_1_9_10_1_625 92 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 257 (accept_3_2 91 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 257 (Polychromatic418967fa.accept_22_1_3_15_1_11046 89 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 257 (accept_3_2 88 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 113 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 257
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 86 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 257 (accept_3_2 85 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 257 (Polychromatic418967fa.accept_10_4_3_7_1_1110 84 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 83 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 257 (accept_3_2 82 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 80 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 257 (accept_3_2 79 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 257 (Polychromatic418967fa.accept_19_2_18_10_1_7366 78 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 257 (Polychromatic418967fa.accept_13_12_9_10_1_1223 77 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 257 (accept_3_2 76 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 75 113
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 257 (accept_3_2 73 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 257 (Polychromatic418967fa.accept_27_18_5_14_1_3959 72 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 257 (Polychromatic418967fa.accept_13_6_9_10_1_1201 71 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 257 (accept_3_2 70 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 113 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 257
  (Polychromatic418967fa.accept_19_11_18_10_1_1148 68 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 113 257 (accept_3_2 67 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 113 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 113 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 113
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 257 (accept_3_2 64 113
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 257
  (Polychromatic418967fa.accept_22_19_3_15_1_14096 63 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 113 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 62 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 257 (accept_3_2 61 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 59 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 257 (accept_3_2 58 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 257 (Polychromatic418967fa.accept_21_15_8_5_1_12668 57 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 257 (Polychromatic418967fa.accept_10_6_3_7_1_2197 56 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 257 (accept_3_2 55 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 257 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 113
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 257 (accept_3_2 52 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 257 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 257 (Polychromatic418967fa.accept_20_10_13_17_1_11451 50 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 257 (accept_3_2 49 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 113 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 257
  (Polychromatic418967fa.accept_19_9_18_10_1_7446 47 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 113 257 (accept_3_2 46 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 113 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 113 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 257 (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 113
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 257 (accept_3_2 43 113
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 257
  (Polychromatic418967fa.accept_17_8_11_2_1_3415 42 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 113 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 113 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 257 (accept_3_2 40 113 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 113 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 38
  113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 257 (accept_3_2 37
  113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 257
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 113 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 113 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 257 (accept_3_2 34 113 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 113 257 (Polychromatic418967fa.accept_19_14_18_10_1_7368 33 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 257 (accept_3_2 31 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 257 (Polychromatic418967fa.accept_19_11_18_10_1_1148 30 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 257 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 257 (accept_3_2 28 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 113 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 257
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 26 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 257 (accept_3_2 25 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 257 (Polychromatic418967fa.accept_21_2_8_5_1_5057 23 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 257 (accept_3_2 22 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 257 (Polychromatic418967fa.accept_15_6_8_2_1_104 21 113
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 257 (accept_3_2 19 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 257 (accept_3_2 16 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 257
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 257 (accept_3_2 13 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 257 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 257 (accept_3_2 10 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 257 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 257
  (Polychromatic418967fa.accept_17_8_11_2_1_3415 8 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 257 (accept_3_2 7 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 257 (accept_3_2 4 113 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 113 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 257
  (Polychromatic418967fa.accept_19_2_18_10_1_7366 2 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 257 (accept_3_2 1 113 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 257 (allA_of_3_0 112 112 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 257
  (allA_succ_of_accept 110 111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 110 111 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 257 (accept_3_2 109 111 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 257 (Polychromatic418967fa.accept_13_4_7_10_1_1200 108 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 107 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 257 (accept_3_2 106 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 257 (accept_3_2 103 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 111 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 101 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 257 (accept_3_2 100 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 99 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 257 (accept_3_2 97 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 95 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 257 (accept_3_2 94 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 93 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 257 (accept_3_2 91 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 89 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 257 (accept_3_2 88 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 257 (accept_3_2 85 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 257 (Polychromatic418967fa.accept_10_4_1_7_1_371 84 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 257 (accept_3_2 82 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 257 (accept_3_2 79 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 257
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 77 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 111 257 (accept_3_2 76 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 111 257 (Polychromatic418967fa.accept_16_11_15_1_1_2074 75 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 74
  111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 257 (accept_3_2 73
  111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 257
  (Polychromatic418967fa.accept_15_12_6_2_1_2760 72 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 111 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 111 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 257 (accept_3_2 70 111 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 68
  111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 257 (accept_3_2 67
  111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 111 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 257 (accept_3_2 64 111 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 257 (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 257 (accept_3_2 61 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 111 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 111 257 (Polychromatic418967fa.accept_16_11_15_1_1_2074 59 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 257 (accept_3_2 58 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 111 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 257 (accept_3_2 55 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 111 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 257 (accept_3_2 52 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 257 (accept_3_2 49 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 111 257 (Polychromatic418967fa.accept_14_6_13_5_1_534 48 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 111 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 257 (accept_3_2 46 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 257 (accept_3_2 43 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 111 257 (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 257 (accept_3_2 40 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 111 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 257 (accept_3_2 37 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 111 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 257 (accept_3_2 34 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 257 (accept_3_2 31 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 257 (accept_3_2 28 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 257 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 111 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 257 (accept_3_2 25 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 257 (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 257 (accept_3_2 22 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 111
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 257 (accept_3_2 19 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 257 (accept_3_2 16 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 257 (accept_3_2 13 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 257 (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 257 (accept_3_2 10 111 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 257 (accept_3_2 7 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 257 (Polychromatic418967fa.accept_16_5_15_1_1_2113 5 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 257 (accept_3_2 4 111 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 257 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 111 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 257 (accept_3_2 1 111 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 257 (allA_succ_of_accept 109 110 257 (accept_3_2 109 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 257 (Polychromatic418967fa.accept_13_4_6_10_1_1199 108 110 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 257 (Polychromatic418967fa.accept_4_3_2_1_1_50
  107 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 110 257 (accept_3_2
  106 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 110 257
  (Polychromatic418967fa.accept_6_3_2_5_1_32 105 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 110 257 (Polychromatic418967fa.accept_12_8_2_5_1_844 104 110 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 110 257 (accept_3_2 103 110 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 110 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 102 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 110 257
  (Polychromatic418967fa.accept_14_3_12_5_1_153 101 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 110 257 (accept_3_2 100 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 110 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 110 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 110 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 110 257 (accept_3_2 97 110 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 110 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 96 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 110 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 110 257 (accept_3_2 94 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 110 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 110 257 (Polychromatic418967fa.accept_12_8_2_5_1_844 92 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 257 (accept_3_2 91 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 110 257 (Polychromatic418967fa.accept_13_12_6_10_1_667 90 110
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 110 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 89 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 110 257 (accept_3_2 88 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 110 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 110 257 (Polychromatic418967fa.accept_15_11_5_2_1_520 86 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 110 257 (accept_3_2 85 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 110 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 110 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 110 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 110 257 (accept_3_2 82 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 110 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 110 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 110 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 110 257 (accept_3_2 79 110 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 110 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 257
  (Polychromatic418967fa.accept_13_12_6_10_1_667 77 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 110 257 (accept_3_2 76 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 110 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 110 257 (Polychromatic418967fa.accept_13_9_6_10_1_666 74 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 257 (accept_3_2 73 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 257 (Polychromatic418967fa.accept_15_12_5_2_1_2786 72 110
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 110 257 (accept_3_2 70 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 110 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 110 257 (Polychromatic418967fa.accept_12_8_2_5_1_844 68 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 257 (accept_3_2 67 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 110 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 110 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 110 257
  (Polychromatic418967fa.accept_20_5_10_17_1_11478 65 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 110 257 (accept_3_2 64 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 110 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 110 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 110 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 257 (accept_3_2 61 110 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 110 257 (Polychromatic418967fa.accept_9_6_2_5_1_506
  60 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 110 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 257 (accept_3_2 58 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 257 (Polychromatic418967fa.accept_12_8_2_5_1_844 56 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 110 257 (accept_3_2 55 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 110 257 (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 110
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 110 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 110 257 (accept_3_2 52 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 110 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 110 257 (Polychromatic418967fa.accept_17_16_8_2_1_5890 50 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 110 257 (accept_3_2 49 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 110 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 257 (accept_3_2 46 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 110 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 110 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 110 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 257 (accept_3_2 43 110 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 257
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 41 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 110 257 (accept_3_2 40 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 110 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 110 257 (Polychromatic418967fa.accept_13_12_6_10_1_667 38 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 257 (accept_3_2 37 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 257 (Polychromatic418967fa.accept_16_4_14_1_1_1241 36 110
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 110 257 (accept_3_2 34 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 110 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 110 257 (Polychromatic418967fa.accept_12_8_2_5_1_844 32 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 257 (accept_3_2 31 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 110 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 110 257
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 29 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 110 257 (accept_3_2 28 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 110 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 110 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 110 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 257 (accept_3_2 25 110 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 257 (accept_3_2 22 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 110 257 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 257 (accept_3_2 19 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 257 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 110
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 257 (accept_3_2 16 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 257 (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 257 (accept_3_2 13 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 110 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 110 257 (accept_3_2 10 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  110 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 110 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 110 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 257 (accept_3_2 7 110 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 257
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 257 (accept_3_2 4 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 257 (Polychromatic418967fa.accept_13_2_6_10_1_2703 2 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 257 (accept_3_2 1 110 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 110
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 257 (allA_of_3_0 109 109 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 257
  (allA_succ_of_accept 107 108 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 107 108 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 257 (accept_3_2 106 108 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 108 257 (Polychromatic418967fa.accept_10_5_8_7_1_2174 105 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 257
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 104 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 108 257 (accept_3_2 103 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 108 257 (Polychromatic418967fa.accept_13_11_4_10_1_3440 102 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 257 (Polychromatic418967fa.accept_8_5_4_1_1_111
  101 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 257 (accept_3_2
  100 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 99 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 108 257 (Polychromatic418967fa.accept_13_7_4_10_1_2675 98 108 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 108 257 (accept_3_2 97 108 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 108 257 (Polychromatic418967fa.accept_13_5_4_10_1_1244 96 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 108 257
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 95 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 108 257 (accept_3_2 94 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 108 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 93 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 108 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 92 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 108 257 (accept_3_2 91 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 108 257 (Polychromatic418967fa.accept_11_2_9_4_1_310 90 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 108 257
  (Polychromatic418967fa.accept_10_9_8_7_1_714 89 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 108 257 (accept_3_2 88 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 108 257 (Polychromatic418967fa.accept_15_12_3_2_1_2756 87 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 108 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 86 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 108 257 (accept_3_2 85 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 108 257 (Polychromatic418967fa.accept_13_6_4_10_1_660 84 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 257
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 83 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 108 257 (accept_3_2 82 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 108 257 (Polychromatic418967fa.accept_17_13_6_2_1_5850 81 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 108 257 (Polychromatic418967fa.accept_15_5_3_2_1_5930 80 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 108 257 (accept_3_2 79 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 108 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 108 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 77 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 108 257 (accept_3_2 76 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 108 257 (Polychromatic418967fa.accept_10_5_8_7_1_2174 75 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 108 257 (Polychromatic418967fa.accept_15_14_3_2_1_2811 74 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 257 (accept_3_2 73 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 108 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 108 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 71 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 108 257 (accept_3_2 70 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 108 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 108 257 (Polychromatic418967fa.accept_11_2_9_4_1_310 68 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 257 (accept_3_2 67 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 108 257 (Polychromatic418967fa.accept_13_1_4_10_1_622 66 108
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 108 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 108 257 (accept_3_2 64 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 108 257 (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 108 257 (Polychromatic418967fa.accept_19_5_13_10_1_11674 62 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 257 (accept_3_2 61 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 108 257 (Polychromatic418967fa.accept_13_8_4_10_1_4358 60 108
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 108 257
  (Polychromatic418967fa.accept_10_9_8_7_1_714 59 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 108 257 (accept_3_2 58 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 108 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 108 257 (Polychromatic418967fa.accept_16_8_12_1_1_7720 56 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 257 (accept_3_2 55 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 257 (Polychromatic418967fa.accept_14_12_10_5_1_2712 54 108
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 108 257 (accept_3_2 52 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 108 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 108 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 257 (accept_3_2 49 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 257 (Polychromatic418967fa.accept_21_6_3_5_1_8198 48 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 257
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 47 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 108 257 (accept_3_2 46 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 108 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 108 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 257 (accept_3_2 43 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 257 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 108 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 257
  (Polychromatic418967fa.accept_19_3_13_10_1_7461 41 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 108 257 (accept_3_2 40 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 108 257 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 108 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 257 (Polychromatic418967fa.accept_17_4_6_2_1_5871 38 108
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 257 (accept_3_2 37 108
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 108 257 (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 108 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 257 (accept_3_2 34 108 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 108 257 (Polychromatic418967fa.accept_13_7_4_10_1_2675 33 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 257
  (Polychromatic418967fa.accept_13_6_4_10_1_660 32 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 108 257 (accept_3_2 31 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 108 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 108 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 257 (accept_3_2 28 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 257 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 257
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 26 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 108 257 (accept_3_2 25 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 108 257 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 108 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 108 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 257 (accept_3_2 22 108 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 257 (Polychromatic418967fa.accept_8_5_4_1_1_111
  21 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 257
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 20 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 257 (accept_3_2 19 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 108 257 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 108 257 (Polychromatic418967fa.accept_22_17_20_15_1_9459 17 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 257 (accept_3_2 16 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 257
  (Polychromatic418967fa.accept_13_1_4_10_1_622 14 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 257 (accept_3_2 13 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 108 257 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 108 257 (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 257 (accept_3_2 10 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 257 (accept_3_2 7 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  108 257 (Polychromatic418967fa.accept_13_6_4_10_1_660 6 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 108 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 257 (accept_3_2 4 108 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 257 (Polychromatic418967fa.accept_19_3_13_10_1_7461 3 108 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 257 (accept_3_2 1 108 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 257 (allA_succ_of_accept 106 107 257 (accept_3_2 106 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 105 107 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 257 (Polychromatic418967fa.accept_19_9_12_10_1_10393 104
  107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 257 (accept_3_2 103
  107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 101 107 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 257 (accept_3_2 100 107 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 257 (Polychromatic418967fa.accept_17_14_5_2_1_4559 99 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 98 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 257 (accept_3_2 97 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 95 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 257 (accept_3_2 94 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 93 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 92 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 257 (accept_3_2 91 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 257 (Polychromatic418967fa.accept_11_1_8_4_1_717 89 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 257 (accept_3_2 88 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 87 107 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 257 (accept_3_2 85 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 257 (accept_3_2 82 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 257 (accept_3_2 79 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 257 (Polychromatic418967fa.accept_14_7_9_5_1_529 77 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 257 (accept_3_2 76 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 75 107 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 257 (accept_3_2 73 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 257 (Polychromatic418967fa.accept_13_7_3_10_1_656 72 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 257 (Polychromatic418967fa.accept_13_6_3_10_1_698 71 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 257 (accept_3_2 70 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 107 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 257
  (Polychromatic418967fa.accept_19_11_12_10_1_7480 68 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 107 257 (accept_3_2 67 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 107 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 107 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 257 (accept_3_2 64 107 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 257
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 257 (accept_3_2 61 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 257 (accept_3_2 58 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 257 (accept_3_2 55 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 257 (accept_3_2 52 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 257 (accept_3_2 49 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 257 (accept_3_2 46 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 257 (Polychromatic418967fa.accept_16_12_11_1_1_4088 44 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 257 (accept_3_2 43 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 257
  (Polychromatic418967fa.accept_13_2_3_10_1_658 41 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 257 (accept_3_2 40 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 257 (accept_3_2 37 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 257 (Polychromatic418967fa.accept_19_17_12_10_1_7404 36 107 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 257
  (Polychromatic418967fa.accept_14_7_9_5_1_529 35 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 257 (accept_3_2 34 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 257 (accept_3_2 31 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 257 (accept_3_2 28 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 257 (Polychromatic418967fa.accept_19_8_12_10_1_9002 27 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 257 (accept_3_2 25 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 257
  (Polychromatic418967fa.accept_11_1_8_4_1_717 23 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 257 (accept_3_2 22 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 257 (accept_3_2 19 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 257 (accept_3_2 16 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 257 (accept_3_2 13 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 257 (accept_3_2 10 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 257 (Polychromatic418967fa.accept_19_9_12_10_1_10393 9 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 257 (Polychromatic418967fa.accept_18_8_17_5_1_9273 8 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 257 (accept_3_2 7 107 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 257
  (Polychromatic418967fa.accept_24_5_11_17_1_7068 5 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 257 (accept_3_2 4 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 107 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 257 (accept_3_2 1 107 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 257 (allA_of_3_0 106 106 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 257
  (allA_succ_of_accept 104 105 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 105 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 257 (accept_3_2 103 105 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 101 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 257 (accept_3_2 100 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 99 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 257 (accept_3_2 97 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 257 (Polychromatic418967fa.accept_14_12_7_5_1_1107 96 105 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 257
  (Polychromatic418967fa.accept_13_4_1_10_1_693 95 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 257 (accept_3_2 94 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 257 (accept_3_2 91 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 257 (Polychromatic418967fa.accept_11_2_6_4_1_3028 90 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 89 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 257 (accept_3_2 88 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 87 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 257 (accept_3_2 85 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 83 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 257 (accept_3_2 82 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 257 (Polychromatic418967fa.accept_18_9_15_5_1_6551 81 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 257 (accept_3_2 79 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 257 (Polychromatic418967fa.accept_10_8_5_7_1_358 78 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 257
  (Polychromatic418967fa.accept_16_13_9_1_1_3022 77 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 257 (accept_3_2 76 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 257 (accept_3_2 73 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 257 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 257 (accept_3_2 70 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 257 (Polychromatic418967fa.accept_13_4_1_10_1_693 69 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 257 (accept_3_2 67 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 65 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 257 (accept_3_2 64 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 257 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 105 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 257 (accept_3_2 61 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 257 (Polychromatic418967fa.accept_18_6_15_5_1_6563 60 105 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 257
  (Polychromatic418967fa.accept_24_11_9_17_1_8853 59 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 105 257 (accept_3_2 58 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 105 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 257 (accept_3_2 55 105 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 257
  (Polychromatic418967fa.accept_14_12_7_5_1_1107 54 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 105 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 257 (accept_3_2 52 105 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 257 (accept_3_2 49 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 105 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 257 (accept_3_2 46 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 257 (Polychromatic418967fa.accept_16_13_9_1_1_3022 45 105 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 257 (accept_3_2 43 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 105 257 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 105 257 (Polychromatic418967fa.accept_28_13_21_5_1_15675 41 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 257 (accept_3_2 40 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 105 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 257 (accept_3_2 37 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 257 (Polychromatic418967fa.accept_25_11_5_7_1_10494 36 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 257 (accept_3_2 34 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 257 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 257 (accept_3_2 31 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 257 (accept_3_2 28 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 257 (accept_3_2 25 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 257 (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 257 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 257 (accept_3_2 22 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 105 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 257 (accept_3_2 19 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 257 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 257 (accept_3_2 16 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 257 (accept_3_2 13 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 257 (accept_3_2 10 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 257 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 257 (accept_3_2 7 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 257 (Polychromatic418967fa.accept_18_6_15_5_1_6563 6 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 257 (Polychromatic418967fa.accept_16_5_9_1_1_2070 5 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 257 (accept_3_2 4 105 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 257 (accept_3_2 1 105 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 257 (allA_succ_of_accept 103 104 257 (accept_3_2 103 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 102 104 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 257 (Polychromatic418967fa.accept_10_1_4_7_1_374 101 104
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 257 (accept_3_2 100 104
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 257
  (Polychromatic418967fa.accept_6_3_2_5_1_32 99 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 257 (Polychromatic418967fa.accept_11_10_5_4_1_711 98 104 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 257 (accept_3_2 97 104 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 257 (Polychromatic418967fa.accept_19_1_9_10_1_10391 96 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 95 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 104 257 (accept_3_2 94 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 104 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 92 104 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 257 (accept_3_2 91 104 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 104 257 (Polychromatic418967fa.accept_21_6_20_5_1_12663 90 104 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 257
  (Polychromatic418967fa.accept_16_9_8_1_1_1228 89 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 104 257 (accept_3_2 88 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 104 257 (Polychromatic418967fa.accept_12_2_8_5_1_408 86 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 257 (accept_3_2 85 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 104 257 (Polychromatic418967fa.accept_16_4_8_1_1_5257 84 104
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 257
  (Polychromatic418967fa.accept_10_3_4_7_1_353 83 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 257 (accept_3_2 82 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 257 (Polychromatic418967fa.accept_15_5_14_2_1_1876 80 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 257 (accept_3_2 79 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 104 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 104 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 257
  (Polychromatic418967fa.accept_19_1_9_10_1_10391 77 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 104 257 (accept_3_2 76 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 104 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 74 104 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 257 (accept_3_2 73 104 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 257 (Polychromatic418967fa.accept_10_2_4_7_1_352
  72 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 257
  (Polychromatic418967fa.accept_7_1_6_5_1_39 71 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 257 (accept_3_2 70 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 257 (Polychromatic418967fa.accept_16_4_8_1_1_5257 68 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 257 (accept_3_2 67 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 257 (Polychromatic418967fa.accept_29_8_17_25_1_15674 66
  104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 257
  (Polychromatic418967fa.accept_11_10_5_4_1_711 65 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 257 (accept_3_2 64 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 257 (accept_3_2 61 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 104 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 257
  (Polychromatic418967fa.accept_24_11_8_17_1_7015 59 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 104 257 (accept_3_2 58 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 257 (Polychromatic418967fa.accept_19_18_9_10_1_4698 56 104
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 257 (accept_3_2 55 104
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 257
  (Polychromatic418967fa.accept_11_10_5_4_1_711 54 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 104 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 104 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 257 (accept_3_2 52 104 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 50
  104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 257 (accept_3_2 49
  104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 257
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 48 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 104 257 (Polychromatic418967fa.accept_16_15_8_1_1_9959 47 104 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 257 (accept_3_2 46 104 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 257
  (Polychromatic418967fa.accept_16_12_8_1_1_5270 44 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 104 257 (accept_3_2 43 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 104 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 104 257 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 257 (accept_3_2 40 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 104 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 104 257 (accept_3_2 37 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 104 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 104 257 (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 257 (accept_3_2 34 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 104 257 (accept_3_2 31 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 104 257 (Polychromatic418967fa.accept_24_6_8_17_1_13945 30 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 104 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 104 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 257 (accept_3_2 28 104 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 257 (accept_3_2 25 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 257 (Polychromatic418967fa.accept_23_1_12_4_1_12486 24 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 257 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 257 (accept_3_2 22 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 257
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 257 (accept_3_2 19 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 257 (Polychromatic418967fa.accept_22_17_16_15_1_15673 17 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 257 (accept_3_2 16 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 257 (accept_3_2 13 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 104 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 257 (accept_3_2 10 104 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 257
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 257 (accept_3_2 7 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 257 (Polychromatic418967fa.accept_19_6_9_10_1_15672 6 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 257 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 257 (accept_3_2 4 104 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 257
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 257 (accept_3_2 1 104 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 257 (allA_of_3_0 103 103 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 257 (allA_succ_of_accept 101
  102 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 101 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 102 257 (accept_3_2 100 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 102 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 102 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 98 102 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 257 (accept_3_2 97 102 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 257 (Polychromatic418967fa.accept_9_6_3_5_1_240
  96 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 102 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 102 257 (accept_3_2 94 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 102 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 93 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 102 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 92 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 257 (accept_3_2 91 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 90 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 102 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 89 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 102 257 (accept_3_2 88 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 102 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 102 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 86 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 257 (accept_3_2 85 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 84 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 102 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 102 257 (accept_3_2 82 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 102 257 (Polychromatic418967fa.accept_13_3_11_10_1_2647 81 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 102 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 257 (accept_3_2 79 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 102 257
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 77 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 102 257 (accept_3_2 76 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 102 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 102 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 257 (accept_3_2 73 102 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 257 (Polychromatic418967fa.accept_7_2_4_5_1_313
  72 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 102 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 102 257 (accept_3_2 70 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 102 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 102 257 (Polychromatic418967fa.accept_13_3_11_10_1_2647 68 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 257 (accept_3_2 67 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 257 (Polychromatic418967fa.accept_13_1_11_10_1_1258 66 102
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 102 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 65 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 102 257 (accept_3_2 64 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 102 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 102 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 62 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 257 (accept_3_2 61 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 102 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 102 257 (accept_3_2 58 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 102 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 102 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 257 (accept_3_2 55 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 102 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 102 257 (accept_3_2 52 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 102 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 102 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 257 (accept_3_2 49 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 102 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 102 257 (accept_3_2 46 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 102 257 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 102 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 257 (accept_3_2 43 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 102 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 257 (accept_3_2 40 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 102 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 102 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 257 (accept_3_2 37 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 257 (accept_3_2 34 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 102 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 102 257 (Polychromatic418967fa.accept_20_12_2_17_1_1620 32 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 257 (accept_3_2 31 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 102 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 257 (accept_3_2 28 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 102 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 102 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 257 (accept_3_2 25 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 257 (accept_3_2 22 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 102 257 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 102 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 257 (accept_3_2 19 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 257 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 257 (accept_3_2 16 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 102 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 102 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 257 (accept_3_2 13 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 257 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12
  102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 257 (accept_3_2 10 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 257 (accept_3_2 7 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 102 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 257
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 257 (accept_3_2 4 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 257 (accept_3_2 1 102 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 257 (allA_succ_of_accept 100 101 257 (accept_3_2 100 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 99 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 101 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 257 (accept_3_2 97 101 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 257 (Polychromatic418967fa.accept_9_6_2_5_1_506
  96 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 257
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 95 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 257 (accept_3_2 94 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 93 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 92 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 257 (accept_3_2 91 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 257 (Polychromatic418967fa.accept_17_5_16_2_1_7094 90 101 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 89 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 257 (accept_3_2 88 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 87 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 86 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 257 (accept_3_2 85 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 257
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 83 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 257 (accept_3_2 82 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 257 (Polychromatic418967fa.accept_15_6_11_2_1_2801 81 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 257 (accept_3_2 79 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 257
  (Polychromatic418967fa.accept_16_13_5_1_1_3017 77 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 257 (accept_3_2 76 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 101 257 (Polychromatic418967fa.accept_10_4_1_7_1_371 74 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 257 (accept_3_2 73 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 101 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 71 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 257 (accept_3_2 70 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 68 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 257 (accept_3_2 67 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 257 (accept_3_2 64 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 257 (Polychromatic418967fa.accept_16_15_5_1_1_7724 63 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 257 (accept_3_2 61 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 257
  (Polychromatic418967fa.accept_17_8_16_2_1_10847 59 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 101 257 (accept_3_2 58 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 101 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 257 (Polychromatic418967fa.accept_10_6_1_7_1_342 56 101
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 257 (accept_3_2 55 101
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 257
  (Polychromatic418967fa.accept_10_4_1_7_1_371 54 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 101 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 257 (accept_3_2 52 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 101 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 50
  101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 257 (accept_3_2 49
  101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 257
  (Polychromatic418967fa.accept_9_3_2_5_1_234 48 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 101 257 (Polychromatic418967fa.accept_16_15_5_1_1_7724 47 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 257 (accept_3_2 46 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 101 257 (Polychromatic418967fa.accept_16_13_5_1_1_3017 45 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 257 (accept_3_2 43 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 257 (Polychromatic418967fa.accept_16_9_5_1_1_1259 41 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 257 (accept_3_2 40 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 101 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 257
  (Polychromatic418967fa.accept_16_6_5_1_1_7761 38 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 257 (accept_3_2 37 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 257 (accept_3_2 34 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 257
  (Polychromatic418967fa.accept_18_14_11_5_1_7967 32 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 101 257 (accept_3_2 31 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 101 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 101 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 257 (accept_3_2 28 101 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 257
  (Polychromatic418967fa.accept_25_2_1_7_1_12137 27 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 101 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 257 (accept_3_2 25 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 101 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 23
  101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 257 (accept_3_2 22
  101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 257
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 101 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 257 (accept_3_2 19 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 101 257 (Polychromatic418967fa.accept_17_1_16_2_1_1404 18 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 257 (accept_3_2 16 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 257 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 257 (accept_3_2 13 101 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 101 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 257
  (Polychromatic418967fa.accept_20_11_1_17_1_5535 11 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 257 (accept_3_2 10 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 101 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 101 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 257 (accept_3_2 7 101 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 257
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 257 (accept_3_2 4 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 101 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 257 (accept_3_2 1 101 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 257 (allA_of_3_0 100 100 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 257 (allA_succ_of_accept 98 99
  257 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 257 (accept_3_2 97 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96
  99 257 (Polychromatic418967fa.accept_13_5_8_10_1_4363 96 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 99 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 95 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 257 (accept_3_2 94 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 93 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 257 (accept_3_2 91 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 257 (Polychromatic418967fa.accept_13_11_8_10_1_676 89 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 257 (accept_3_2 88 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 99 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 257 (accept_3_2 85 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 257 (Polychromatic418967fa.accept_16_4_3_1_1_8843 84 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 83 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 257 (accept_3_2 82 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 257 (accept_3_2 79 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 257 (Polychromatic418967fa.accept_13_12_8_10_1_1879 77 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 257 (accept_3_2 76 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 257 (Polychromatic418967fa.accept_20_15_19_17_1_722 75 99
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 257 (accept_3_2 73 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 257 (Polychromatic418967fa.accept_15_11_9_2_1_4780 71 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 257 (accept_3_2 70 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 99 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 257 (accept_3_2 67 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 257 (Polychromatic418967fa.accept_19_8_4_10_1_7393 65 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 257 (accept_3_2 64 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 257 (Polychromatic418967fa.accept_13_11_8_10_1_676 63 99
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 257 (accept_3_2 61 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 257 (accept_3_2 58 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 257 (accept_3_2 55 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 257 (accept_3_2 52 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 257 (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 257 (accept_3_2 49 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 257 (Polychromatic418967fa.accept_19_9_4_10_1_7370 47 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 257 (accept_3_2 46 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 99 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 257 (accept_3_2 43 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 257 (accept_3_2 40 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 257 (accept_3_2 37 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 257 (Polychromatic418967fa.accept_16_4_3_1_1_8843 36 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 257 (Polychromatic418967fa.accept_19_16_4_10_1_7474 35 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 257 (accept_3_2 34 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 99 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 257 (accept_3_2 31 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 257 (Polychromatic418967fa.accept_16_13_3_1_1_2100 29 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 257 (accept_3_2 28 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 99 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 257 (accept_3_2 25 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 257 (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 257 (accept_3_2 22 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 257 (accept_3_2 19 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 257 (accept_3_2 16 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 257 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 257 (accept_3_2 13 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 257 (accept_3_2 10 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 99 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 257 (accept_3_2 7 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 257 (Polychromatic418967fa.accept_13_5_8_10_1_4363 5 99 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 257 (accept_3_2 4 99 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 257 (accept_3_2 1 99 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  257 (allA_succ_of_accept 97 98 257 (accept_3_2 97 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 257 (accept_3_2 94 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 92 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 257 (accept_3_2 91 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 257 (Polychromatic418967fa.accept_13_12_7_10_1_2662 90 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 257 (Polychromatic418967fa.accept_10_9_8_7_1_714 89 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 257 (accept_3_2 88 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 257
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 86 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 257 (accept_3_2 85 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 257 (accept_3_2 82 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 257 (accept_3_2 79 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 257 (Polychromatic418967fa.accept_13_12_7_10_1_2662 77 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 257 (accept_3_2 76 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 257 (accept_3_2 73 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 257 (Polychromatic418967fa.accept_19_15_3_10_1_10389 72 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 257 (accept_3_2 70 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 257 (accept_3_2 67 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 257 (accept_3_2 64 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 257
  (Polychromatic418967fa.accept_19_5_3_10_1_4641 62 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 257 (accept_3_2 61 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 257 (accept_3_2 58 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 257 (accept_3_2 55 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 257 (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 257 (Polychromatic418967fa.accept_18_17_8_5_1_2769 53 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 257 (accept_3_2 52 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 257
  (Polychromatic418967fa.accept_18_14_8_5_1_860 50 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 257 (accept_3_2 49 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 257 (accept_3_2 46 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 257 (accept_3_2 43 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 257 (Polychromatic418967fa.accept_16_9_2_1_1_3077 41 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 257 (accept_3_2 40 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 257 (accept_3_2 37 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 257 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 257 (accept_3_2 34 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 257 (accept_3_2 31 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 257 (accept_3_2 28 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 257
  (Polychromatic418967fa.accept_19_7_3_10_1_4674 26 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 257 (accept_3_2 25 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 257 (accept_3_2 22 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 257 (accept_3_2 19 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 257 (Polychromatic418967fa.accept_17_1_13_2_1_7086 18 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 257 (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 257 (accept_3_2 16 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 257
  (Polychromatic418967fa.accept_18_14_8_5_1_860 14 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 257 (accept_3_2 13 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 257 (accept_3_2 10 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 257 (accept_3_2 7 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  257 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 257 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 98 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 257 (accept_3_2 4 98 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  98 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 257 (accept_3_2 1 98 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  257 (allA_of_3_0 97 97 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 257 (allA_succ_of_accept 95 96 257
  (Polychromatic418967fa.accept_11_7_8_4_1_718 95 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 96 257 (accept_3_2 94 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  96 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 96 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 257 (accept_3_2 91 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 257 (Polychromatic418967fa.accept_19_14_1_10_1_11713 90 96 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 96 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 89 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 257 (accept_3_2 88 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  96 257 (Polychromatic418967fa.accept_14_3_12_5_1_153 87 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 96 257 (Polychromatic418967fa.accept_13_8_5_10_1_2701 86 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 257 (accept_3_2 85 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 96 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 96 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 83 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 257 (accept_3_2 82 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  96 257 (Polychromatic418967fa.accept_10_1_6_7_1_710 81 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 96 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 257 (accept_3_2 79 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 257 (Polychromatic418967fa.accept_11_1_8_4_1_717 78 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 96 257
  (Polychromatic418967fa.accept_14_7_12_5_1_1861 77 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 257 (accept_3_2 76 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  96 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 96 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 257 (accept_3_2 73 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 257 (Polychromatic418967fa.accept_15_12_6_2_1_2760 72 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 96 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 257 (accept_3_2 70 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  96 257 (Polychromatic418967fa.accept_13_4_5_10_1_1247 69 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 96 257 (Polychromatic418967fa.accept_15_8_6_2_1_1128 68 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 257 (accept_3_2 67 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 65 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 257 (accept_3_2 64 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  96 257 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 96 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 257 (accept_3_2 61 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 257 (Polychromatic418967fa.accept_13_8_5_10_1_2701 60 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 257
  (Polychromatic418967fa.accept_14_3_12_5_1_153 59 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 257 (accept_3_2 58 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  96 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 96 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 257 (accept_3_2 55 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 257 (Polychromatic418967fa.accept_13_2_5_10_1_250 54 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 96 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 257 (accept_3_2 52 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  96 257 (Polychromatic418967fa.accept_10_1_6_7_1_710 51 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 96 257 (Polychromatic418967fa.accept_21_8_12_5_1_8209 50 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 257 (accept_3_2 49 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 96 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 96 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 257 (accept_3_2 46 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  96 257 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 96 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 257 (accept_3_2 43 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 257 (Polychromatic418967fa.accept_15_12_6_2_1_2760 42 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 257
  (Polychromatic418967fa.accept_10_1_6_7_1_710 41 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 257 (accept_3_2 40 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  96 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 96 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 257 (accept_3_2 37 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 257 (Polychromatic418967fa.accept_19_17_1_10_1_4671 36 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 257 (accept_3_2 34 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 257 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 257 (Polychromatic418967fa.accept_13_6_5_10_1_1213 32 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 257 (accept_3_2 31 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 96 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 257 (accept_3_2 28 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 257 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 257 (accept_3_2 25 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 257 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 257
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 257 (accept_3_2 22 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 257 (accept_3_2 19 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 257 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 257 (accept_3_2 16 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 257 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 257 (Polychromatic418967fa.accept_19_14_1_10_1_11713 14 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 257 (accept_3_2 13 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 96 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 257 (accept_3_2 10 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 257 (Polychromatic418967fa.accept_17_9_11_2_1_5894 9 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 257 (accept_3_2 7 96 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 257 (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 96 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 257
  (Polychromatic418967fa.accept_22_5_8_15_1_15671 5 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 257 (accept_3_2 4 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  257 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 96 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 257 (accept_3_2 1 96 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 257
  (allA_succ_of_accept 94 95 257 (accept_3_2 94 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 93 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 92 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 257 (accept_3_2 91 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 257
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 89 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 257 (accept_3_2 88 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 257 (Polychromatic418967fa.accept_15_12_5_2_1_2786 87 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 257 (accept_3_2 85 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 257 (Polychromatic418967fa.accept_13_6_4_10_1_660 84 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 83 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 257 (accept_3_2 82 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 257 (Polychromatic418967fa.accept_21_18_11_5_1_3487 81 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 257 (Polychromatic418967fa.accept_11_3_7_4_1_1133 80 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 257 (accept_3_2 79 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 257
  (Polychromatic418967fa.accept_21_14_11_5_1_6591 77 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 257 (accept_3_2 76 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 257 (Polychromatic418967fa.accept_16_11_15_1_1_2074 75 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 257 (accept_3_2 73 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 257 (accept_3_2 70 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 257 (Polychromatic418967fa.accept_10_8_5_7_1_358 68 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 257 (accept_3_2 67 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 65 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 257 (accept_3_2 64 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 257 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 257 (accept_3_2 61 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 257 (Polychromatic418967fa.accept_13_8_4_10_1_4358 60 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 257
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 59 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 257 (accept_3_2 58 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 257 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 257 (accept_3_2 55 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 257
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 257 (accept_3_2 52 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 257 (accept_3_2 49 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 257
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 47 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 257 (accept_3_2 46 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 257 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 257 (accept_3_2 43 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 257 (accept_3_2 40 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 257 (Polychromatic418967fa.accept_20_19_15_17_1_7059 39 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 257 (accept_3_2 37 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 257
  (Polychromatic418967fa.accept_21_14_11_5_1_6591 35 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 257 (accept_3_2 34 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 257 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 257 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 257 (accept_3_2 31 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 257 (accept_3_2 28 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 257 (accept_3_2 25 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 257 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 257 (accept_3_2 22 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 257 (Polychromatic418967fa.accept_13_8_4_10_1_4358 21 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 257 (accept_3_2 19 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 257
  (Polychromatic418967fa.accept_21_17_11_5_1_5060 17 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 257 (accept_3_2 16 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 257 (accept_3_2 13 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 257 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 257
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 257 (accept_3_2 10 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 257 (accept_3_2 7 95 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 257
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 257 (accept_3_2 4 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  257 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 95 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 257 (accept_3_2 1 95 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 257
  (allA_of_3_0 94 94 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 257 (allA_succ_of_accept 92 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 257 (accept_3_2 91 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 257 (Polychromatic418967fa.accept_13_12_2_10_1_2698 90 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 89 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 257 (accept_3_2 88 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 87 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 257 (accept_3_2 85 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 83 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 257 (accept_3_2 82 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 257 (accept_3_2 79 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 257 (Polychromatic418967fa.accept_13_12_2_10_1_2698 77 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 257 (accept_3_2 76 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 75 93 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 257 (accept_3_2 73 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 257 (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 257 (accept_3_2 70 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 257 (accept_3_2 67 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 257 (accept_3_2 64 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 257 (accept_3_2 61 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 257 (accept_3_2 58 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 257 (Polychromatic418967fa.accept_13_5_2_10_1_248 57 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 257 (accept_3_2 55 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 257 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 257 (accept_3_2 52 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 257 (accept_3_2 49 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 257 (Polychromatic418967fa.accept_22_4_5_15_1_15670 48 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 257 (accept_3_2 46 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 257 (accept_3_2 43 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 257 (Polychromatic418967fa.accept_16_9_13_1_1_3069 41 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 257 (accept_3_2 40 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 93 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 257 (accept_3_2 37 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 257 (accept_3_2 34 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 257 (accept_3_2 31 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 257 (Polychromatic418967fa.accept_16_14_13_1_1_5278 30 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 257 (accept_3_2 28 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 257 (accept_3_2 25 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 257 (Polychromatic418967fa.accept_19_4_17_10_1_4632 23 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 257 (accept_3_2 22 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 257 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 93 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 257 (accept_3_2 19 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 257 (accept_3_2 16 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 257 (accept_3_2 13 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 257 (accept_3_2 10 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 257 (Polychromatic418967fa.accept_16_9_13_1_1_3069 9 93 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 257 (accept_3_2 7 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  257 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 93 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 93 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 257 (accept_3_2 4 93 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 93 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 257 (accept_3_2 1 93 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 257
  (allA_succ_of_accept 91 92 257 (accept_3_2 91 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 257 (accept_3_2 88 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 86 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 257 (accept_3_2 85 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 83 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 257 (accept_3_2 82 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 80 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 257 (accept_3_2 79 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 77 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 257 (accept_3_2 76 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 257 (accept_3_2 73 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 257 (Polychromatic418967fa.accept_16_8_12_1_1_7720 72 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 257 (accept_3_2 70 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 257
  (Polychromatic418967fa.accept_16_4_12_1_1_1204 68 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 257 (accept_3_2 67 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 257 (Polychromatic418967fa.accept_10_5_2_7_1_345 65 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 257 (accept_3_2 64 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 257 (accept_3_2 61 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 257 (accept_3_2 58 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 257
  (Polychromatic418967fa.accept_13_4_1_10_1_693 56 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 257 (accept_3_2 55 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 257 (accept_3_2 52 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 257 (accept_3_2 49 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 257 (Polychromatic418967fa.accept_17_13_7_2_1_4562 47 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 257 (accept_3_2 46 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 257 (accept_3_2 43 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 257 (accept_3_2 40 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 257 (accept_3_2 37 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 257 (Polychromatic418967fa.accept_16_4_12_1_1_1204 36 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 257 (accept_3_2 34 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 257 (accept_3_2 31 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 257 (accept_3_2 28 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 257 (accept_3_2 25 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 257 (Polychromatic418967fa.accept_19_4_16_10_1_2171 23 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 257 (accept_3_2 22 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 257 (accept_3_2 19 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 257 (accept_3_2 16 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 257
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 257 (accept_3_2 13 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 257 (accept_3_2 10 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 257 (accept_3_2 7 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 92 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 257 (accept_3_2 4 92 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 257 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  92 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 257 (accept_3_2 1 92 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 257
  (allA_of_3_0 91 91 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 257 (allA_succ_of_accept 89 90 257
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 89 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 90 257 (accept_3_2 88 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 90 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 257 (Polychromatic418967fa.accept_11_9_2_4_1_707 86 90 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 257 (accept_3_2 85 90 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 257 (Polychromatic418967fa.accept_13_6_12_10_1_690
  84 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 90 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 90 257 (accept_3_2 82 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  90 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 90 257 (Polychromatic418967fa.accept_13_2_12_10_1_2649 80 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 257 (accept_3_2 79 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 90 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 257
  (Polychromatic418967fa.accept_19_1_14_10_1_4619 77 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 257 (accept_3_2 76 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  90 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 90 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 74 90 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 257 (accept_3_2 73 90 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 257 (Polychromatic418967fa.accept_11_6_2_4_1_1703 72 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 257 (accept_3_2 70 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  90 257 (Polychromatic418967fa.accept_14_13_6_5_1_1853 69 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 90 257 (Polychromatic418967fa.accept_20_8_10_17_1_12884 68 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 257 (accept_3_2 67 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 257 (Polychromatic418967fa.accept_21_3_6_5_1_8187 66 90 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 257
  (Polychromatic418967fa.accept_17_14_5_2_1_4559 65 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 90 257 (accept_3_2 64 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  90 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 90 257 (Polychromatic418967fa.accept_19_5_14_10_1_8933 62 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 257 (accept_3_2 61 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 90 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 257 (accept_3_2 58 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  90 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 90 257 (Polychromatic418967fa.accept_19_18_14_10_1_10403 56 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 257 (accept_3_2 55 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 257 (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 90
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 53 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 257 (accept_3_2 52 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  90 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 90 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 90 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 257 (accept_3_2 49 90 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 257 (Polychromatic418967fa.accept_13_9_12_10_1_242 48 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 257 (accept_3_2 46 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  90 257 (Polychromatic418967fa.accept_13_6_12_10_1_690 45 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 90 257 (Polychromatic418967fa.accept_19_6_14_10_1_4624 44 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 257 (accept_3_2 43 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 257 (Polychromatic418967fa.accept_11_9_2_4_1_707 42 90 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 257
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 41 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 257 (accept_3_2 40 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  90 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 90 257 (Polychromatic418967fa.accept_20_18_10_17_1_11450 38 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 257 (accept_3_2 37 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 90 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 90 257 (accept_3_2 34 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  90 257 (Polychromatic418967fa.accept_13_7_12_10_1_640 33 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 90 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 90 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 257 (accept_3_2 31 90 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 257 (Polychromatic418967fa.accept_22_8_2_15_1_6041 30 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 257
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 257 (accept_3_2 28 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  90 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 90 257 (Polychromatic418967fa.accept_19_7_14_10_1_6034 26 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 257 (accept_3_2 25 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 257 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 90
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 257 (accept_3_2 22 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 257 (Polychromatic418967fa.accept_13_8_12_10_1_4414 21 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 257 (Polychromatic418967fa.accept_11_9_2_4_1_707 20 90 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 257 (accept_3_2 19 90 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 257
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 257 (accept_3_2 16 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 257 (Polychromatic418967fa.accept_17_14_5_2_1_4559 14 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 257 (accept_3_2 13 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 257 (Polychromatic418967fa.accept_19_12_14_10_1_4625 12 90
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 257 (accept_3_2 10 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 257 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 90 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 90 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 257 (accept_3_2 7 90 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 257 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 90 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 257
  (Polychromatic418967fa.accept_19_5_14_10_1_8933 5 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 257 (accept_3_2 4 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90
  257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 257 (Polychromatic418967fa.accept_13_2_12_10_1_2649 2 90 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 257 (accept_3_2 1 90 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 90 257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 89 257 (allA_succ_of_accept 88 89 257 (accept_3_2 88 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 87 89 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 257 (Polychromatic418967fa.accept_13_8_11_10_1_636 86 89
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 257 (accept_3_2 85 89 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 84
  89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 83 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 257 (accept_3_2 82 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 257 (Polychromatic418967fa.accept_13_3_11_10_1_2647 81 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 257 (Polychromatic418967fa.accept_13_2_11_10_1_1881 80 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 257 (accept_3_2 79 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 89 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 257
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 77 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 89 257 (accept_3_2 76 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 89 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 75 89 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 89 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 89 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 257 (accept_3_2 73 89 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 257 (Polychromatic418967fa.accept_10_2_9_7_1_720
  72 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 257
  (Polychromatic418967fa.accept_22_5_1_15_1_15669 71 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 257 (accept_3_2 70 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 257 (Polychromatic418967fa.accept_10_8_9_7_1_1118 68 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 257 (accept_3_2 67 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 257 (accept_3_2 64 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 257 (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 62 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 257 (accept_3_2 61 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 257
  (Polychromatic418967fa.accept_19_2_13_10_1_14204 59 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 89 257 (accept_3_2 58 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 89 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 89 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 89 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 257 (accept_3_2 55 89 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 257
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 54 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 89 257 (Polychromatic418967fa.accept_13_1_11_10_1_1258 53 89 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 257 (accept_3_2 52 89 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 89 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 257 (Polychromatic418967fa.accept_15_5_14_2_1_1876
  50 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 257 (accept_3_2 49
  89 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 257
  (Polychromatic418967fa.accept_9_3_8_5_1_65 48 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 89 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 89 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 257 (accept_3_2 46 89 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 89 257 (Polychromatic418967fa.accept_16_13_9_1_1_3022 45 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 257
  (Polychromatic418967fa.accept_18_8_17_5_1_9273 44 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 257 (accept_3_2 43 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 257 (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 257 (accept_3_2 40 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 257 (accept_3_2 37 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 257 (Polychromatic418967fa.accept_22_14_1_15_1_6055 36 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 257 (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 257 (accept_3_2 34 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 89 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 257
  (Polychromatic418967fa.accept_10_2_9_7_1_720 32 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 257 (accept_3_2 31 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 257 (accept_3_2 28 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 257 (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 257
  (Polychromatic418967fa.accept_16_10_9_1_1_9973 26 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 257 (accept_3_2 25 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 257 (Polychromatic418967fa.accept_17_6_4_2_1_5889 23 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 257 (accept_3_2 22 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 257 (accept_3_2 19 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 257 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 257 (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 257 (accept_3_2 16 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 89 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 257
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 14 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 257 (accept_3_2 13 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 257 (accept_3_2 10 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 257 (Polychromatic418967fa.accept_17_9_4_2_1_2298 9 89 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 257
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 257 (accept_3_2 7 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  257 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 257 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 89 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 257 (accept_3_2 4 89 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 89 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  89 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 257 (accept_3_2 1 89 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 257
  (allA_of_3_0 88 88 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 257 (allA_succ_of_accept 86 87 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 87 257 (accept_3_2 85 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  87 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 87 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 257 (accept_3_2 82 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 257 (accept_3_2 79 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 257 (Polychromatic418967fa.accept_13_12_9_10_1_1223 77 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 257 (accept_3_2 76 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 87 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 257 (accept_3_2 73 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 257 (accept_3_2 70 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 69 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 257 (accept_3_2 67 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 257 (accept_3_2 64 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 257 (accept_3_2 61 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 257 (Polychromatic418967fa.accept_11_5_10_4_1_1157 60 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 257 (Polychromatic418967fa.accept_15_14_12_2_1_3804 59 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 257 (accept_3_2 58 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 87 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 257 (accept_3_2 55 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 257 (accept_3_2 52 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 257 (accept_3_2 49 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 257 (accept_3_2 46 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 257 (accept_3_2 43 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 257 (Polychromatic418967fa.accept_19_3_11_10_1_2184 41 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 257 (accept_3_2 40 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 87 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 257 (accept_3_2 37 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 257 (accept_3_2 34 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 257 (accept_3_2 31 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 257 (accept_3_2 28 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 257 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 257 (accept_3_2 25 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 257 (Polychromatic418967fa.accept_16_8_7_1_1_8875 24 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 257 (accept_3_2 22 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 257 (accept_3_2 19 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 257 (accept_3_2 16 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 257 (accept_3_2 13 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 257 (accept_3_2 10 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 87 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 257 (accept_3_2 7 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 257 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 87 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 257 (accept_3_2 4 87 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 257 (accept_3_2 1 87 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 257
  (allA_succ_of_accept 85 86 257 (accept_3_2 85 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 257 (Polychromatic418967fa.accept_15_9_11_2_1_1882 84 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 257 (accept_3_2 82 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 257 (accept_3_2 79 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 257 (Polychromatic418967fa.accept_24_6_14_17_1_15668 78 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 257 (Polychromatic418967fa.accept_13_12_8_10_1_1879 77 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 257 (accept_3_2 76 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 74 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 257 (accept_3_2 73 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 257 (Polychromatic418967fa.accept_13_7_8_10_1_2663 72 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 257 (accept_3_2 70 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 257
  (Polychromatic418967fa.accept_11_2_9_4_1_310 68 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 257 (accept_3_2 67 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 257 (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 257 (accept_3_2 64 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 257
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 62 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 257 (accept_3_2 61 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 257 (accept_3_2 58 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 257 (accept_3_2 55 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 257 (Polychromatic418967fa.accept_13_2_8_10_1_1902 54 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 257 (accept_3_2 52 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 257
  (Polychromatic418967fa.accept_13_11_8_10_1_676 50 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 257 (accept_3_2 49 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 257 (Polychromatic418967fa.accept_22_4_20_15_1_7892 48 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 257 (accept_3_2 46 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 257 (accept_3_2 43 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 257 (Polychromatic418967fa.accept_25_17_11_7_1_15667 42 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 257 (Polychromatic418967fa.accept_10_1_6_7_1_710 41 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 257 (accept_3_2 40 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 257 (accept_3_2 37 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 257 (Polychromatic418967fa.accept_15_6_11_2_1_2801 36 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 257 (accept_3_2 34 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 257 (accept_3_2 31 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 257 (Polychromatic418967fa.accept_13_4_8_10_1_671 30 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 257 (Polychromatic418967fa.accept_18_11_14_5_1_3951 29 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 257 (accept_3_2 28 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 257
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 26 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 257 (accept_3_2 25 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 257 (accept_3_2 22 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 257 (accept_3_2 19 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 257 (accept_3_2 16 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 257
  (Polychromatic418967fa.accept_23_14_17_4_1_15666 14 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 86 257 (accept_3_2 13 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 86 257 (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 86 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 257 (accept_3_2 10 86 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 257 (accept_3_2 7 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  257 (Polychromatic418967fa.accept_15_6_11_2_1_2801 6 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 86 257 (Polychromatic418967fa.accept_13_5_8_10_1_4363 5 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 257 (accept_3_2 4 86 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 86 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 257
  (Polychromatic418967fa.accept_11_2_9_4_1_310 2 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 86 257 (accept_3_2 1 86 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 257
  (allA_of_3_0 85 85 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 257 (allA_succ_of_accept 83 84 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 257 (accept_3_2 82 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 257 (Polychromatic418967fa.accept_10_1_4_7_1_374 81 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 257 (accept_3_2 79 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 77 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 257 (accept_3_2 76 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 257 (Polychromatic418967fa.accept_19_18_8_10_1_7489 75 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 257 (accept_3_2 73 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 257 (accept_3_2 70 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 257 (Polychromatic418967fa.accept_13_3_6_10_1_2658 68 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 257 (accept_3_2 67 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 257 (Polychromatic418967fa.accept_24_18_12_17_1_10620 66 84
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 257 (accept_3_2 64 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 257 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 257 (accept_3_2 61 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 257
  (Polychromatic418967fa.accept_17_8_16_2_1_10847 59 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 257 (accept_3_2 58 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 257 (Polychromatic418967fa.accept_13_5_6_10_1_2659 57 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 257 (accept_3_2 55 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 257 (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 257 (accept_3_2 52 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 257 (Polychromatic418967fa.accept_19_12_8_10_1_8948 50 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 257 (accept_3_2 49 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 257 (Polychromatic418967fa.accept_13_9_6_10_1_666 48 84 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 257 (accept_3_2 46 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 257 (accept_3_2 43 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 257
  (Polychromatic418967fa.accept_10_1_4_7_1_374 41 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 257 (accept_3_2 40 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 257 (Polychromatic418967fa.accept_17_5_16_2_1_7094 39 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 257 (accept_3_2 37 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 257 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 257 (accept_3_2 34 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 257 (accept_3_2 31 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 257 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 257 (accept_3_2 28 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 257 (Polychromatic418967fa.accept_18_9_12_5_1_864 27 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 257 (accept_3_2 25 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 257
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 257 (accept_3_2 22 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 257 (accept_3_2 19 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 257 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 257 (accept_3_2 16 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 257 (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 257 (accept_3_2 13 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 257 (accept_3_2 10 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 257 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 257 (accept_3_2 7 84 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 84 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 257 (accept_3_2 4 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  257 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 84 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 84 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 84 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 257 (accept_3_2 1 84 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 257 (allA_succ_of_accept 82 83 257 (accept_3_2 82 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 83 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 83 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 257 (accept_3_2 79 83 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 78
  83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 257
  (Polychromatic418967fa.accept_16_13_3_1_1_2100 77 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 257 (accept_3_2 76 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 257 (accept_3_2 73 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 257 (Polychromatic418967fa.accept_17_4_15_2_1_4551 72 83 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 257
  (Polychromatic418967fa.accept_7_1_6_5_1_39 71 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 257 (accept_3_2 70 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 257 (Polychromatic418967fa.accept_11_2_6_4_1_3028 68 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 257 (accept_3_2 67 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 257
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 257 (accept_3_2 64 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 257 (Polychromatic418967fa.accept_23_17_14_4_1_15665 63 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 257 (accept_3_2 61 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 83 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 257
  (Polychromatic418967fa.accept_23_13_14_4_1_12470 59 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 83 257 (accept_3_2 58 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 83 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 83 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 83 257 (Polychromatic418967fa.accept_10_6_3_7_1_2197 56 83 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 257 (accept_3_2 55 83 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 53 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 257 (accept_3_2 52 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 257 (accept_3_2 49 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 257
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 47 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 257 (accept_3_2 46 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 257 (accept_3_2 43 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 257
  (Polychromatic418967fa.accept_13_2_5_10_1_250 41 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 257 (accept_3_2 40 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 257 (accept_3_2 37 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 83 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 257 (accept_3_2 34 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 257 (accept_3_2 31 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 257
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 257 (accept_3_2 28 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 257 (Polychromatic418967fa.accept_17_10_15_2_1_653 27 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 257 (accept_3_2 25 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 83 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 257
  (Polychromatic418967fa.accept_21_2_20_5_1_6599 23 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 257 (accept_3_2 22 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 257 (Polychromatic418967fa.accept_14_6_13_5_1_534 20 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 257 (accept_3_2 19 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 257 (accept_3_2 16 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 257 (accept_3_2 13 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 83 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 257 (accept_3_2 10 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 257 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 257 (accept_3_2 7 83 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 257
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 257 (accept_3_2 4 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  257 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 83 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 257 (accept_3_2 1 83 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 257 (allA_of_3_0 82 82 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 257
  (allA_succ_of_accept 80 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 257 (accept_3_2 79 81 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 257
  (Polychromatic418967fa.accept_21_14_18_5_1_8196 77 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 257 (accept_3_2 76 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  81 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 257 (accept_3_2 73 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 81 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 81 257 (accept_3_2 70 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  81 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 257 (accept_3_2 67 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 257 (Polychromatic418967fa.accept_10_6_1_7_1_342 66 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 65 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 257 (accept_3_2 64 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  81 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 257 (accept_3_2 61 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 257 (Polychromatic418967fa.accept_19_3_5_10_1_6033 60 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 257
  (Polychromatic418967fa.accept_13_7_3_10_1_656 59 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 257 (accept_3_2 58 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 257 (accept_3_2 55 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 257 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 257
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 257 (accept_3_2 52 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 257 (accept_3_2 49 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 257
  (Polychromatic418967fa.accept_23_1_12_4_1_12486 47 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 257 (accept_3_2 46 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 257 (Polychromatic418967fa.accept_13_6_3_10_1_698 45 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 257 (accept_3_2 43 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 257 (Polychromatic418967fa.accept_15_12_6_2_1_2760 42 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 257 (accept_3_2 40 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 257 (accept_3_2 37 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 257
  (Polychromatic418967fa.accept_17_1_13_2_1_7086 35 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 257 (accept_3_2 34 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 257 (Polychromatic418967fa.accept_13_7_3_10_1_656 33 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 257 (accept_3_2 31 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 257 (accept_3_2 28 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 257 (accept_3_2 25 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 257 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 257 (accept_3_2 22 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 257 (Polychromatic418967fa.accept_19_2_5_10_1_4608 21 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 257 (accept_3_2 19 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 257 (Polychromatic418967fa.accept_17_1_13_2_1_7086 18 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 257
  (Polychromatic418967fa.accept_25_17_6_7_1_12113 17 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 257 (accept_3_2 16 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 257 (accept_3_2 13 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 257 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 257
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 257 (accept_3_2 10 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 257 (accept_3_2 7 81 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 81 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 257
  (Polychromatic418967fa.accept_24_5_9_17_1_8872 5 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 257 (accept_3_2 4 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  257 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 81 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 257 (accept_3_2 1 81 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 257 (allA_succ_of_accept 79 80 257 (accept_3_2 79 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 80 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 80 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 80 257 (Polychromatic418967fa.accept_13_12_2_10_1_2698 77 80
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 257 (accept_3_2 76 80 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 75
  80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 257 (accept_3_2 73 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 257 (accept_3_2 70 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 257
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 68 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 257 (accept_3_2 67 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 257 (accept_3_2 64 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 257
  (Polychromatic418967fa.accept_11_7_3_4_1_729 62 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 257 (accept_3_2 61 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 257 (Polychromatic418967fa.accept_15_14_5_2_1_4761 59 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 257 (accept_3_2 58 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 257 (accept_3_2 55 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 257 (Polychromatic418967fa.accept_14_12_10_5_1_2712 54 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 257 (Polychromatic418967fa.accept_18_17_8_5_1_2769 53 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 257 (accept_3_2 52 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 257 (accept_3_2 49 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 257 (accept_3_2 46 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 257 (accept_3_2 43 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 257 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 257 (accept_3_2 40 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 257 (accept_3_2 37 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 257 (Polychromatic418967fa.accept_18_17_8_5_1_2769 35 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 257 (accept_3_2 34 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 257
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 32 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 257 (accept_3_2 31 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 257 (accept_3_2 28 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 257 (accept_3_2 25 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 257 (accept_3_2 22 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 257 (accept_3_2 19 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 257 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 257 (Polychromatic418967fa.accept_18_17_8_5_1_2769 17 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 257 (accept_3_2 16 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 257 (accept_3_2 13 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 257 (accept_3_2 10 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 257 (accept_3_2 7 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  257 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 80 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 257 (Polychromatic418967fa.accept_13_5_2_10_1_248 5 80 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 257 (accept_3_2 4 80 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 80
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 257 (accept_3_2 1 80 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 257 (allA_of_3_0 79
  79 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 257 (allA_succ_of_accept 77 78 257
  (Polychromatic418967fa.accept_16_13_14_1_1_2094 77 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 257 (accept_3_2 76 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 74 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 257 (accept_3_2 73 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 257 (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 257 (accept_3_2 70 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 257 (Polychromatic418967fa.accept_16_4_14_1_1_1241 68 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 257 (accept_3_2 67 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 78 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 65 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 257 (accept_3_2 64 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 62 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 257 (accept_3_2 61 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 257 (accept_3_2 58 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 257 (accept_3_2 55 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 257 (Polychromatic418967fa.accept_21_12_15_5_1_12686 54 78 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 257 (accept_3_2 52 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 257 (Polychromatic418967fa.accept_15_5_3_2_1_5930 50 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 257 (accept_3_2 49 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 257 (accept_3_2 46 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 257 (accept_3_2 43 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 257 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 257 (accept_3_2 40 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 257 (accept_3_2 37 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 257 (Polychromatic418967fa.accept_16_4_14_1_1_1241 36 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 257 (accept_3_2 34 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 257 (Polychromatic418967fa.accept_18_15_6_5_1_3972 33 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 257 (accept_3_2 31 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 257 (accept_3_2 28 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 257 (accept_3_2 25 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 257 (accept_3_2 22 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 257 (accept_3_2 19 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 257 (accept_3_2 16 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 257 (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 257 (accept_3_2 13 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 78 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 257 (accept_3_2 10 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 257 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 78 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 257 (accept_3_2 7 78 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 78 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 257
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 257 (accept_3_2 4 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 78 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 257 (accept_3_2 1 78 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  77 257 (allA_succ_of_accept 76 77 257 (accept_3_2 76 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 77 257 (Polychromatic418967fa.accept_17_7_9_2_1_629 75 77 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 77 257 (Polychromatic418967fa.accept_13_9_12_10_1_242 74 77
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 257 (accept_3_2 73 77 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 257 (Polychromatic418967fa.accept_13_7_12_10_1_640
  72 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 257
  (Polychromatic418967fa.accept_13_6_12_10_1_690 71 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 257 (accept_3_2 70 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 257 (Polychromatic418967fa.accept_16_5_13_1_1_2084 69 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 68 77 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 257 (accept_3_2 67 77 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 257 (Polychromatic418967fa.accept_19_9_1_10_1_4606 66 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 257
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 65 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 257 (accept_3_2 64 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 257 (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 257 (Polychromatic418967fa.accept_16_14_13_1_1_5278 62 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 257 (accept_3_2 61 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 77 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 257
  (Polychromatic418967fa.accept_13_7_12_10_1_640 59 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 257 (accept_3_2 58 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 257 (Polychromatic418967fa.accept_16_9_13_1_1_3069 57 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 257 (Polychromatic418967fa.accept_22_12_11_15_1_15664 56 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 257 (accept_3_2 55 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 257 (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 77
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 257
  (Polychromatic418967fa.accept_16_5_13_1_1_2084 53 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 257 (accept_3_2 52 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 257 (Polychromatic418967fa.accept_14_9_7_5_1_1105 51 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 257 (Polychromatic418967fa.accept_13_11_12_10_1_2652 50 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 257 (accept_3_2 49 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 257 (Polychromatic418967fa.accept_13_9_12_10_1_242 48 77
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 257
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 47 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 257 (accept_3_2 46 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 257 (Polychromatic418967fa.accept_13_6_12_10_1_690 45 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 77 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 257 (accept_3_2 43 77 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 257 (Polychromatic418967fa.accept_19_4_1_10_1_7447 42 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 257
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 41 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 257 (accept_3_2 40 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 257 (Polychromatic418967fa.accept_21_18_14_5_1_8193 39 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 257 (Polychromatic418967fa.accept_17_4_9_2_1_9721 38 77 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 257 (accept_3_2 37 77 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 257
  (Polychromatic418967fa.accept_13_9_12_10_1_242 35 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 257 (accept_3_2 34 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 257 (Polychromatic418967fa.accept_13_7_12_10_1_640 33 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 257 (Polychromatic418967fa.accept_13_6_12_10_1_690 32 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 257 (accept_3_2 31 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 257 (Polychromatic418967fa.accept_14_2_7_5_1_5450 30 77 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 257
  (Polychromatic418967fa.accept_21_8_14_5_1_8177 29 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 257 (accept_3_2 28 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 257 (Polychromatic418967fa.accept_22_5_11_15_1_7870 27 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 257 (Polychromatic418967fa.accept_14_12_7_5_1_1107 26 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 257 (accept_3_2 25 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 257 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 77
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 257
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 257 (accept_3_2 22 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 257 (Polychromatic418967fa.accept_13_8_12_10_1_4414 21 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 77 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 257 (accept_3_2 19 77 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 257 (Polychromatic418967fa.accept_21_18_14_5_1_8193 18 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 257
  (Polychromatic418967fa.accept_19_17_1_10_1_4671 17 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 257 (accept_3_2 16 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 257 (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 257 (Polychromatic418967fa.accept_16_14_13_1_1_5278 14 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 257 (accept_3_2 13 77 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 77 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 257
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 77 257 (accept_3_2 10 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 77 257 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 77 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 257 (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 77 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 257 (accept_3_2 7 77 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 257 (Polychromatic418967fa.accept_13_6_12_10_1_690
  6 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 257
  (Polychromatic418967fa.accept_16_5_13_1_1_2084 5 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 257 (accept_3_2 4 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  257 (Polychromatic418967fa.accept_16_3_13_1_1_1206 3 77 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 77 257 (Polychromatic418967fa.accept_13_2_12_10_1_2649 2 77 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 257 (accept_3_2 1 77 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 77 257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 76 257 (allA_of_3_0 76 76 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 257
  (allA_succ_of_accept 74 75 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 257 (accept_3_2 73 75 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 75 257 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 71
  75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 257 (accept_3_2 70 75
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 257
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 257 (accept_3_2 67 75 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 65
  75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 257 (accept_3_2 64 75
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 257
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 75 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 257 (accept_3_2 61 75 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 75 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 257
  (Polychromatic418967fa.accept_19_2_18_10_1_7366 59 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 75 257 (accept_3_2 58 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  75 257 (Polychromatic418967fa.accept_11_2_9_4_1_310 57 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 75 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 257 (accept_3_2 55 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 257 (accept_3_2 52 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  75 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 75 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 257 (accept_3_2 49 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 257 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 75 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 257 (accept_3_2 46 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  75 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 75 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 257 (accept_3_2 43 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 257
  (Polychromatic418967fa.accept_28_13_19_5_1_15663 41 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 75 257 (accept_3_2 40 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 75 257 (Polychromatic418967fa.accept_20_19_15_17_1_7059 39 75 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 257 (accept_3_2 37 75 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 257
  (Polychromatic418967fa.accept_19_17_18_10_1_7485 36 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 257 (accept_3_2 34 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 257 (accept_3_2 31 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 257 (accept_3_2 28 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 257 (Polychromatic418967fa.accept_19_8_18_10_1_3360 27 75 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 257 (accept_3_2 25 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 257 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 257 (accept_3_2 22 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 75 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 257 (accept_3_2 19 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 257 (accept_3_2 16 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 75 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 257 (accept_3_2 13 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 257 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 257 (accept_3_2 10 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 75 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 257 (accept_3_2 7 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 257 (Polychromatic418967fa.accept_19_5_18_10_1_4604 5 75 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 257 (accept_3_2 4 75 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 257 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 75 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 257 (accept_3_2 1 75 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 257 (allA_succ_of_accept
  73 74 257 (accept_3_2 73 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 72 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 257 (accept_3_2 70 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 257 (Polychromatic418967fa.accept_12_8_2_5_1_844
  68 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 257 (accept_3_2 67
  74 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 257
  (Polychromatic418967fa.accept_9_3_2_5_1_234 66 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 257 (accept_3_2 64 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 62
  74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 257 (accept_3_2 61 74
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 257
  (Polychromatic418967fa.accept_9_6_2_5_1_506 60 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 257 (accept_3_2 58 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 257 (Polychromatic418967fa.accept_11_1_8_4_1_717
  56 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 257 (accept_3_2 55
  74 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 257
  (Polychromatic418967fa.accept_21_12_11_5_1_6549 54 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 257 (accept_3_2 52 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 50
  74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 257 (accept_3_2 49 74
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 257 (accept_3_2 46 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 44
  74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 257 (accept_3_2 43 74
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 257
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 257 (accept_3_2 40 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 257
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 38 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 257 (accept_3_2 37 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 257 (accept_3_2 34 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 74 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 257
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 257 (accept_3_2 31 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 257 (accept_3_2 28 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 257 (accept_3_2 25 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 257 (accept_3_2 22 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 257 (accept_3_2 19 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 257 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 257 (accept_3_2 16 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 257
  (Polychromatic418967fa.accept_13_1_9_10_1_625 14 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 257 (accept_3_2 13 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 257 (accept_3_2 10 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 257 (accept_3_2 7 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 257 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 257 (accept_3_2 4 74 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  74 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 257 (accept_3_2 1 74 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 257 (allA_of_3_0 73 73 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 257 (allA_succ_of_accept 71 72 257
  (Polychromatic418967fa.accept_16_7_8_1_1_3061 71 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 257 (accept_3_2 70 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 257 (Polychromatic418967fa.accept_10_9_2_7_1_1096 69 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 257 (Polychromatic418967fa.accept_11_2_6_4_1_3028 68 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 257 (accept_3_2 67 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 257
  (Polychromatic418967fa.accept_10_5_2_7_1_345 65 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 257 (accept_3_2 64 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 257 (Polychromatic418967fa.accept_14_7_2_5_1_4528 63 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 257 (Polychromatic418967fa.accept_19_5_15_10_1_7405 62 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 257 (accept_3_2 61 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 72 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 257 (accept_3_2 58 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 257 (Polychromatic418967fa.accept_11_2_6_4_1_3028 57 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 257 (Polychromatic418967fa.accept_13_4_7_10_1_1200 56 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 257 (accept_3_2 55 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 72 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 257 (accept_3_2 52 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 257 (Polychromatic418967fa.accept_13_12_7_10_1_2662 51 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 257 (Polychromatic418967fa.accept_15_5_12_2_1_2820 50 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 257 (accept_3_2 49 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 72 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 257
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 47 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 257 (accept_3_2 46 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 257 (accept_3_2 43 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 257 (Polychromatic418967fa.accept_13_3_7_10_1_668 42 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 257
  (Polychromatic418967fa.accept_16_9_8_1_1_1228 41 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 257 (accept_3_2 40 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 257 (accept_3_2 37 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 257 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 257
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 257 (accept_3_2 34 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 257 (accept_3_2 31 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 257 (Polychromatic418967fa.accept_13_4_7_10_1_1200 30 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 257
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 257 (accept_3_2 28 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 257 (Polychromatic418967fa.accept_20_7_12_17_1_8580 27 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 257 (Polychromatic418967fa.accept_17_9_4_2_1_2298 26 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 257 (accept_3_2 25 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 257
  (Polychromatic418967fa.accept_16_7_8_1_1_3061 23 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 257 (accept_3_2 22 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 257 (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 257 (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 257 (accept_3_2 19 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 72 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 257 (accept_3_2 16 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 257 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 257 (accept_3_2 13 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 257 (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 257 (accept_3_2 10 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 257 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 257 (Polychromatic418967fa.accept_13_8_7_10_1_4362 8 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 257 (accept_3_2 7 72 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 257 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 72 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 257
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 257 (accept_3_2 4 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  257 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 257 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 72 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 257 (accept_3_2 1 72 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 257
  (allA_succ_of_accept 70 71 257 (accept_3_2 70 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 257 (Polychromatic418967fa.accept_13_3_6_10_1_2658 68 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 257 (accept_3_2 67 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 257 (accept_3_2 64 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 257 (Polychromatic418967fa.accept_19_6_14_10_1_4624 63 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 257 (accept_3_2 61 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 59 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 257 (accept_3_2 58 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 257 (accept_3_2 55 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 257 (accept_3_2 52 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 257 (accept_3_2 49 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 257 (accept_3_2 46 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 257 (Polychromatic418967fa.accept_10_4_1_7_1_371 44 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 257 (accept_3_2 43 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 257 (accept_3_2 40 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 257 (accept_3_2 37 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 257 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 257
  (Polychromatic418967fa.accept_13_9_6_10_1_666 35 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 257 (accept_3_2 34 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 257 (accept_3_2 31 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 257 (accept_3_2 28 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 257 (accept_3_2 25 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 257
  (Polychromatic418967fa.accept_19_4_14_10_1_7467 23 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 257 (accept_3_2 22 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 257 (accept_3_2 19 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 257 (accept_3_2 16 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 257 (accept_3_2 13 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 257 (accept_3_2 10 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 257 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 257 (Polychromatic418967fa.accept_16_8_7_1_1_8875 8 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 257 (accept_3_2 7 71 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 257
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 257 (accept_3_2 4 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  257 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 71 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 257 (accept_3_2 1 71 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 257
  (allA_of_3_0 70 70 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 257 (allA_succ_of_accept 68 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 257 (accept_3_2 67 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 257 (accept_3_2 64 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 257 (accept_3_2 61 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 257 (Polychromatic418967fa.accept_13_7_4_10_1_2675 59 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 257 (accept_3_2 58 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 69 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 257 (accept_3_2 55 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 257 (Polychromatic418967fa.accept_16_6_5_1_1_7761 54 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 257 (accept_3_2 52 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 257 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 257 (accept_3_2 49 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 257 (accept_3_2 46 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 257 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 257 (accept_3_2 43 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 257 (Polychromatic418967fa.accept_15_11_9_2_1_4780 41 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 257 (accept_3_2 40 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 69 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 257 (accept_3_2 37 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 257 (accept_3_2 34 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 257 (Polychromatic418967fa.accept_13_7_4_10_1_2675 33 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 257 (accept_3_2 31 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 257 (accept_3_2 28 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 257 (accept_3_2 25 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 257 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 257 (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 257 (accept_3_2 22 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 257 (accept_3_2 19 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 257 (accept_3_2 16 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 257 (accept_3_2 13 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 257 (accept_3_2 10 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 257 (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 257 (accept_3_2 7 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  257 (Polychromatic418967fa.accept_13_6_4_10_1_660 6 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 69 257 (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 257 (accept_3_2 4 69 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 69 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 257 (accept_3_2 1 69 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 257 (allA_succ_of_accept 67 68
  257 (accept_3_2 67 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 257
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 66 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 257 (Polychromatic418967fa.accept_10_5_8_7_1_2174 65 68 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 257 (accept_3_2 64 68 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 257 (Polychromatic418967fa.accept_12_2_8_5_1_408
  62 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 257 (accept_3_2 61
  68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 257
  (Polychromatic418967fa.accept_16_12_4_1_1_1257 60 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 257 (Polychromatic418967fa.accept_10_9_8_7_1_714 59 68 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 257 (accept_3_2 58 68 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 257 (Polychromatic418967fa.accept_16_8_4_1_1_2102
  56 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 257 (accept_3_2 55
  68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 257
  (Polychromatic418967fa.accept_13_2_3_10_1_658 54 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 68 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 257 (accept_3_2 52 68 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 257 (Polychromatic418967fa.accept_11_6_2_4_1_1703
  50 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 257 (accept_3_2 49
  68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 257
  (Polychromatic418967fa.accept_25_23_18_7_1_15662 48 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 257 (Polychromatic418967fa.accept_18_11_14_5_1_3951 47 68 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 257 (accept_3_2 46 68 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 257
  (Polychromatic418967fa.accept_16_12_4_1_1_1257 44 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 257 (accept_3_2 43 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 257 (Polychromatic418967fa.accept_11_9_2_4_1_707 42 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 257 (Polychromatic418967fa.accept_13_2_3_10_1_658 41 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 257 (accept_3_2 40 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 257 (accept_3_2 37 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 257 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 257 (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 257 (accept_3_2 34 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 257
  (Polychromatic418967fa.accept_13_6_3_10_1_698 32 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 257 (accept_3_2 31 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 257 (Polychromatic418967fa.accept_16_14_4_1_1_3049 30 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 257 (accept_3_2 28 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 257 (accept_3_2 25 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 257 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 257 (Polychromatic418967fa.accept_22_1_2_15_1_15661 23 68 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 257 (accept_3_2 22 68 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 257
  (Polychromatic418967fa.accept_11_9_2_4_1_707 20 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 257 (accept_3_2 19 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 257 (Polychromatic418967fa.accept_19_18_11_10_1_7379 18 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 257 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 257 (accept_3_2 16 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 257 (accept_3_2 13 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 257 (Polychromatic418967fa.accept_16_12_4_1_1_1257 12 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 257 (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 68 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 257 (accept_3_2 10 68 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 257
  (Polychromatic418967fa.accept_16_8_4_1_1_2102 8 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 257 (accept_3_2 7 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  257 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 68 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 257 (accept_3_2 4 68 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 68 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 68 257 (accept_3_2 1 68 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 257 (allA_of_3_0 67 67 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 257 (allA_succ_of_accept 65 66 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 257 (accept_3_2 64 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 257 (accept_3_2 61 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 257 (accept_3_2 58 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 257 (accept_3_2 55 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 257 (Polychromatic418967fa.accept_14_12_10_5_1_2712 54 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 257 (accept_3_2 52 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 257 (accept_3_2 49 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 257 (Polychromatic418967fa.accept_13_9_1_10_1_647 48 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 257 (accept_3_2 46 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 257 (Polychromatic418967fa.accept_18_9_12_5_1_864 45 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 257 (accept_3_2 43 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 257
  (Polychromatic418967fa.accept_10_1_6_7_1_710 41 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 257 (accept_3_2 40 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 257 (accept_3_2 37 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 257 (accept_3_2 34 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 257 (Polychromatic418967fa.accept_19_13_9_10_1_2181 32 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 257 (accept_3_2 31 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 66 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 257 (accept_3_2 28 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 257 (accept_3_2 25 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 257 (accept_3_2 22 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 257 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 257 (accept_3_2 19 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 257 (Polychromatic418967fa.accept_19_18_9_10_1_4698 18 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 257 (accept_3_2 16 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 257 (Polychromatic418967fa.accept_31_14_4_9_1_15660 14 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 257 (accept_3_2 13 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 257 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 66
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 257 (accept_3_2 10 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 257 (accept_3_2 7 66 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 66 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 257
  (Polychromatic418967fa.accept_31_5_4_9_1_15659 5 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 257 (accept_3_2 4 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 66 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 257 (accept_3_2 1 66 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 257
  (allA_succ_of_accept 64 65 257 (accept_3_2 64 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 257 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 257 (accept_3_2 61 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 257 (accept_3_2 58 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 257 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 257 (accept_3_2 55 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 257 (Polychromatic418967fa.accept_17_3_14_2_1_646 54 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 257 (accept_3_2 52 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 257 (Polychromatic418967fa.accept_17_16_14_2_1_5841 50 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 257 (accept_3_2 49 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 65 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 257
  (Polychromatic418967fa.accept_23_1_19_4_1_15658 47 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 257 (accept_3_2 46 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 257 (accept_3_2 43 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 257
  (Polychromatic418967fa.accept_15_11_5_2_1_520 41 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 257 (accept_3_2 40 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 257 (accept_3_2 37 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 257 (Polychromatic418967fa.accept_19_17_8_10_1_7457 36 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 257 (accept_3_2 34 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 257 (accept_3_2 31 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 257
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 257 (accept_3_2 28 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 257 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 257 (accept_3_2 25 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 257
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 257 (accept_3_2 22 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 257 (Polychromatic418967fa.accept_17_3_14_2_1_646 20 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 257 (accept_3_2 19 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 257 (accept_3_2 16 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 257 (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 257 (accept_3_2 13 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 65 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 257 (accept_3_2 10 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 257 (Polychromatic418967fa.accept_23_9_19_4_1_15657 9 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 257 (accept_3_2 7 65 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 65 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 257
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 257 (accept_3_2 4 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  257 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 65 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 257 (Polychromatic418967fa.accept_10_2_5_7_1_1124 2 65 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 257 (accept_3_2 1 65 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 257
  (allA_of_3_0 64 64 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 257 (allA_succ_of_accept 62 63 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 257 (accept_3_2 61 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 257 (Polychromatic418967fa.accept_13_8_11_10_1_636 60 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 257 (Polychromatic418967fa.accept_15_14_3_2_1_2811 59 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 257 (accept_3_2 58 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 63 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 257 (accept_3_2 55 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 257 (Polychromatic418967fa.accept_13_1_11_10_1_1258 53 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 257 (accept_3_2 52 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 257 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 63 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 257 (accept_3_2 49 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 257 (Polychromatic418967fa.accept_18_12_9_5_1_2771 48 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 257 (Polychromatic418967fa.accept_13_8_11_10_1_636 47 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 257 (accept_3_2 46 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 63 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 257 (accept_3_2 43 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 257 (Polychromatic418967fa.accept_13_2_11_10_1_1881 41 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 257 (accept_3_2 40 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 257 (Polychromatic418967fa.accept_19_1_6_10_1_3366 39 63
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 257 (accept_3_2 37 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 257 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 63 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 257 (accept_3_2 34 63 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 257 (accept_3_2 31 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 257 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 63 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 257 (accept_3_2 28 63 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 257 (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 257 (accept_3_2 25 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 257 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 257 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 63 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 257 (accept_3_2 22 63 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 257 (accept_3_2 19 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 257 (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 257 (accept_3_2 16 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 63 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 257 (accept_3_2 13 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 257 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 257 (Polychromatic418967fa.accept_16_11_15_1_1_2074 11 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 257 (accept_3_2 10 63 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 257 (accept_3_2 7 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 63 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 257 (accept_3_2 4 63 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 257 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 63 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 257 (accept_3_2 1 63 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 257 (allA_succ_of_accept 61 62 257
  (accept_3_2 61 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 257 (accept_3_2 58 62 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 56
  62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 257 (accept_3_2 55 62
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 257
  (Polychromatic418967fa.accept_10_4_2_7_1_373 54 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 62 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 257 (accept_3_2 52 62 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 50
  62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 257 (accept_3_2 49 62
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 257 (Polychromatic418967fa.accept_9_3_8_5_1_65
  48 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 62 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 62 257 (accept_3_2 46 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  62 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 62 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 257 (accept_3_2 43 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 62 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 62 257
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 41 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 62 257 (accept_3_2 40 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  62 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 62 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 257 (accept_3_2 37 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 62 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 257 (accept_3_2 34 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 257 (accept_3_2 31 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 62 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 257
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 257 (accept_3_2 28 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 257 (Polychromatic418967fa.accept_17_9_11_2_1_5894 26 62 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 257 (accept_3_2 25 62 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 62 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 257 (accept_3_2 22 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 257 (accept_3_2 19 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 62 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 257
  (Polychromatic418967fa.accept_18_17_8_5_1_2769 17 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 257 (accept_3_2 16 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 257 (accept_3_2 13 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 62 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 257 (accept_3_2 10 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 62 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 257 (accept_3_2 7 62 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 62 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 257
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 257 (accept_3_2 4 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 62 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 257 (accept_3_2 1 62 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 257
  (allA_of_3_0 61 61 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 60 257 (allA_succ_of_accept 59 60 257
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 59 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 257 (accept_3_2 58 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 257 (accept_3_2 55 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 257 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 60 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 257 (accept_3_2 52 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 257 (accept_3_2 49 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 60 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 257 (accept_3_2 46 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 257 (accept_3_2 43 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 257 (Polychromatic418967fa.accept_23_19_14_4_1_5683 42 60 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 257 (accept_3_2 40 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 257 (accept_3_2 37 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 60 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 257 (accept_3_2 34 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 257 (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 257 (Polychromatic418967fa.accept_11_10_5_4_1_711 32 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 257 (accept_3_2 31 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 60 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 257 (accept_3_2 28 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 257 (accept_3_2 25 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 257 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 60 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 257 (accept_3_2 22 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 257 (accept_3_2 19 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 257 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 60 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 257 (accept_3_2 16 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 257 (Polychromatic418967fa.accept_21_14_18_5_1_8196 14 60 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 257 (accept_3_2 13 60 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 60 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 257 (accept_3_2 10 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 257 (accept_3_2 7 60 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 60 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 257 (accept_3_2 4 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  257 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 60 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 257 (accept_3_2 1 60 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 257
  (allA_succ_of_accept 58 59 257 (accept_3_2 58 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 257 (Polychromatic418967fa.accept_13_4_7_10_1_1200 56 59 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 257 (accept_3_2 55 59 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 257
  (Polychromatic418967fa.accept_21_11_17_5_1_8161 53 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 257 (accept_3_2 52 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 257 (accept_3_2 49 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 257 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 59 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 257
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 47 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 257 (accept_3_2 46 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 257 (Polychromatic418967fa.accept_17_11_8_2_1_3398 45 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 257 (accept_3_2 43 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 257
  (Polychromatic418967fa.accept_25_16_9_7_1_15656 41 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 257 (accept_3_2 40 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 257 (Polychromatic418967fa.accept_25_14_9_7_1_6660 39 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 257 (accept_3_2 37 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 59 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 257
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 257 (accept_3_2 34 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 257 (Polychromatic418967fa.accept_15_3_14_2_1_1888 33 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 257 (accept_3_2 31 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 257 (accept_3_2 28 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 257 (Polychromatic418967fa.accept_15_12_14_2_1_3794 27 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 257 (accept_3_2 25 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 257 (Polychromatic418967fa.accept_19_5_2_10_1_3371 24 59 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 257 (accept_3_2 22 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 257 (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 257 (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 59 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 257 (accept_3_2 19 59 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 257
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 257 (accept_3_2 16 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 257 (accept_3_2 13 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 59 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 257
  (Polychromatic418967fa.accept_17_11_8_2_1_3398 11 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 257 (accept_3_2 10 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 257 (accept_3_2 7 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 257
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 257 (accept_3_2 4 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  257 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 59 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 257 (accept_3_2 1 59 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 257
  (allA_of_3_0 58 58 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 257 (allA_succ_of_accept 56 57 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 257 (accept_3_2 55 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 257 (Polychromatic418967fa.accept_13_2_5_10_1_250 54 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 257 (accept_3_2 52 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 57 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 257 (accept_3_2 49 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 257 (accept_3_2 46 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 257 (accept_3_2 43 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 257 (accept_3_2 40 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 57 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 257 (accept_3_2 37 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 257 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 257 (accept_3_2 34 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 57 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 257 (accept_3_2 31 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 257 (Polychromatic418967fa.accept_13_4_5_10_1_1247 30 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 257 (accept_3_2 28 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 57 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 257 (accept_3_2 25 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 257 (Polychromatic418967fa.accept_27_23_3_14_1_15655 23 57 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 257 (accept_3_2 22 57 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 257 (Polychromatic418967fa.accept_13_8_5_10_1_2701 21 57
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 257 (accept_3_2 19 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 257 (accept_3_2 16 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 257 (accept_3_2 13 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 257 (Polychromatic418967fa.accept_17_12_6_2_1_2346 12 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 257 (accept_3_2 10 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 257 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 57 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 257 (accept_3_2 7 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 257 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 57 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 257 (accept_3_2 4 57 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 57 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 257 (accept_3_2 1 57 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 257 (allA_succ_of_accept 55 56 257 (accept_3_2 55 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 257 (Polychromatic418967fa.accept_15_9_11_2_1_1882 54 56 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 257 (accept_3_2 52 56 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 257 (accept_3_2 49 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 257 (Polychromatic418967fa.accept_13_8_4_10_1_4358 47 56 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 257 (accept_3_2 46 56 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 257 (accept_3_2 43 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 257 (Polychromatic418967fa.accept_10_1_6_7_1_710 41 56 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 257 (accept_3_2 40 56 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 257 (accept_3_2 37 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 257 (Polychromatic418967fa.accept_15_6_11_2_1_2801 36 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 257 (accept_3_2 34 56 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 257
  (Polychromatic418967fa.accept_13_6_4_10_1_660 32 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 257 (accept_3_2 31 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 257 (Polychromatic418967fa.accept_21_8_14_5_1_8177 29 56 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 257 (accept_3_2 28 56 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 257 (accept_3_2 25 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 257 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 56 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 257 (accept_3_2 22 56 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 257
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 20 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 257 (accept_3_2 19 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 257 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 257 (accept_3_2 16 56 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 257 (accept_3_2 13 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 257 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 56 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 257 (accept_3_2 10 56 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 257 (accept_3_2 7 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  257 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 257 (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 56 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 257 (accept_3_2 4 56 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 257 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  56 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 257 (accept_3_2 1 56 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 257))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 257 (allA_of_3_0 55 55 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 257
  (allA_succ_of_accept 53 54 257 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 54 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 257 (accept_3_2 52 54 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 257
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 50 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 54 257 (accept_3_2 49 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  54 257 (Polychromatic418967fa.accept_17_14_3_2_1_5848 48 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 54 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 257 (accept_3_2 46 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 54 257 (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 54 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 257
  (Polychromatic418967fa.accept_13_5_2_10_1_248 44 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 257 (accept_3_2 43 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  54 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 54 257 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 257 (accept_3_2 40 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 54 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 257
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 38 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 257 (accept_3_2 37 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  54 257 (Polychromatic418967fa.accept_21_15_12_5_1_9766 36 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 54 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 257 (accept_3_2 34 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 257 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 54 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 257
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 257 (accept_3_2 31 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  54 257 (Polychromatic418967fa.accept_21_9_12_5_1_317 30 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 54 257 (Polychromatic418967fa.accept_13_3_2_10_1_2697 29 54 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 257 (accept_3_2 28 54 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 257
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 257 (accept_3_2 25 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  54 257 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 257 (accept_3_2 22 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 257 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 54 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 257
  (Polychromatic418967fa.accept_19_1_16_10_1_6026 20 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 257 (accept_3_2 19 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 257 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 257 (Polychromatic418967fa.accept_14_3_12_5_1_153 17 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 257 (accept_3_2 16 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 257
  (Polychromatic418967fa.accept_17_14_3_2_1_5848 14 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 257 (accept_3_2 13 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 257 (accept_3_2 10 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 257 (Polychromatic418967fa.accept_19_9_16_10_1_4701 9 54 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 257
  (Polychromatic418967fa.accept_13_8_2_10_1_652 8 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 257 (accept_3_2 7 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  257 (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 54 257 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 257 (accept_3_2 4 54 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 257
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 257 (accept_3_2 1 54 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 257 (allA_succ_of_accept 52 53 257 (accept_3_2
  52 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 53 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 257 (accept_3_2 49 53 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 53 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 47
  53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 257 (accept_3_2 46 53
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 257
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 53 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 257 (accept_3_2 43 53 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 41
  53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 257 (accept_3_2 40 53
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 257 (Polychromatic418967fa.accept_9_3_8_5_1_65
  39 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 257 (accept_3_2 37 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 53 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 257 (accept_3_2 34 53 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 53 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 257
  (Polychromatic418967fa.accept_27_5_26_14_1_15654 32 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 53 257 (accept_3_2 31 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 53 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 53 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 53 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 257 (accept_3_2 28 53 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 27
  53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 257
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 26 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 257 (accept_3_2 25 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 53 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 257 (accept_3_2 22 53 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 53 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 257 (accept_3_2 19 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 257 (Polychromatic418967fa.accept_21_18_11_5_1_3487 18 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 257 (Polychromatic418967fa.accept_13_4_1_10_1_693 17 53 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 257 (accept_3_2 16 53 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 53 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 257
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 257 (accept_3_2 13 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 257 (accept_3_2 10 53 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 53 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 257 (accept_3_2 7 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 53 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 257 (accept_3_2 4 53 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 53 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  53 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 257 (accept_3_2 1 53 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 257)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 257 (allA_of_3_0 52 52 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 257
  (allA_succ_of_accept 50 51 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 257 (accept_3_2 49 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 51 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 47
  51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 257 (accept_3_2 46 51
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 257 (accept_3_2 43 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 257 (Polychromatic418967fa.accept_11_8_7_4_1_3011
  41 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 257 (accept_3_2 40
  51 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 257 (accept_3_2 37 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 257 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 51 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 35
  51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 257 (accept_3_2 34 51
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 257
  (Polychromatic418967fa.accept_12_9_3_5_1_423 33 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 257 (accept_3_2 31 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 29
  51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 257 (accept_3_2 28 51
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 257
  (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 257 (accept_3_2 25 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 257 (Polychromatic418967fa.accept_15_8_6_2_1_1128
  23 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 257 (accept_3_2 22
  51 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 257
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 257 (accept_3_2 19 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 257 (accept_3_2 16 51
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 257
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 257 (accept_3_2 13 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 51 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 11
  51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 257 (accept_3_2 10 51
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 257
  (Polychromatic418967fa.accept_12_9_3_5_1_423 9 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 257 (accept_3_2 7 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 51 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 257
  (Polychromatic418967fa.accept_19_5_13_10_1_11674 5 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 257 (accept_3_2 4 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  257 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 257 (accept_3_2 1 51 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 257))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 257 (allA_succ_of_accept
  49 50 257 (accept_3_2 49 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 257 (accept_3_2 46 50 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 50 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 257 (Polychromatic418967fa.accept_12_8_2_5_1_844
  44 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 257 (accept_3_2 43
  50 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 257
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 42 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 50 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 257 (accept_3_2 40 50 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 38
  50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 257 (accept_3_2 37 50
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 257
  (Polychromatic418967fa.accept_19_17_12_10_1_7404 36 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 257 (accept_3_2 34 50 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 257 (accept_3_2 31 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 257 (Polychromatic418967fa.accept_13_4_11_10_1_1226 30 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 257 (Polychromatic418967fa.accept_13_3_11_10_1_2647 29 50 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 257 (accept_3_2 28 50 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 257
  (Polychromatic418967fa.accept_15_11_5_2_1_520 26 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 257 (accept_3_2 25 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 257 (accept_3_2 22 50 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 257 (accept_3_2 19 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 50 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 257 (accept_3_2 16 50 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 257
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 14 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 257 (accept_3_2 13 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 257 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 257 (accept_3_2 10 50 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 257 (accept_3_2 7 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 257 (Polychromatic418967fa.accept_17_5_16_2_1_7094 5 50 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 257 (accept_3_2 4 50 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 257 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2
  50 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 257 (accept_3_2 1 50 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 257)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 257 (allA_of_3_0 49 49 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 257 (allA_succ_of_accept 47 48
  257 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 257 (accept_3_2 46 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 257 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 257 (accept_3_2 43 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 48 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 257
  (Polychromatic418967fa.accept_14_13_6_5_1_1853 41 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 257 (accept_3_2 40 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 257 (accept_3_2 37 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 48 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 257 (accept_3_2 34 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 257 (accept_3_2 31 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 257 (Polychromatic418967fa.accept_20_10_8_17_1_12900 30 48 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 257
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 257 (accept_3_2 28 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 257 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 257 (accept_3_2 25 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 48 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 257
  (Polychromatic418967fa.accept_27_23_21_14_1_15653 23 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 48 257 (accept_3_2 22 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 48 257 (Polychromatic418967fa.accept_22_21_4_15_1_9443 21 48 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 48 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 257 (accept_3_2 19 48 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 18
  48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 257 (accept_3_2 16 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 257 (Polychromatic418967fa.accept_13_1_9_10_1_625 14 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 257 (accept_3_2 13 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 257 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 48 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 257 (accept_3_2 10 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 257 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 257 (accept_3_2 7 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 48 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 257
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 257 (accept_3_2 4 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  257 (Polychromatic418967fa.accept_17_3_14_2_1_646 3 48 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 48 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 257 (accept_3_2 1 48 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 48 257)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 257
  (allA_succ_of_accept 46 47 257 (accept_3_2 46 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 257 (Polychromatic418967fa.accept_19_7_9_10_1_4600 45 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 47 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 257 (accept_3_2 43 47 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 257
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 41 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 257 (accept_3_2 40 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 257 (accept_3_2 37 47 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 257 (Polychromatic418967fa.accept_20_16_7_17_1_5459 36 47 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 257 (accept_3_2 34 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 257 (Polychromatic418967fa.accept_17_15_13_2_1_3418 32 47 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 257 (accept_3_2 31 47 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 257
  (Polychromatic418967fa.accept_11_7_3_4_1_729 29 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 257 (accept_3_2 28 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 257 (Polychromatic418967fa.accept_16_11_15_1_1_2074 27 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 257 (accept_3_2 25 47 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 257
  (Polychromatic418967fa.accept_17_6_13_2_1_4549 23 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 257 (accept_3_2 22 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 257 (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 47 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 257 (accept_3_2 19 47 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 257 (accept_3_2 16 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 257 (accept_3_2 13 47 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 257
  (Polychromatic418967fa.accept_13_11_8_10_1_676 11 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 257 (accept_3_2 10 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 257 (Polychromatic418967fa.accept_20_9_7_17_1_1655 9 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 47 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 257 (accept_3_2 7 47 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 257
  (Polychromatic418967fa.accept_13_5_8_10_1_4363 5 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 257 (accept_3_2 4 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  257 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 47 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 257 (accept_3_2 1 47 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 257))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 257 (allA_of_3_0 46 46 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 257 (allA_succ_of_accept 44 45 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 257 (accept_3_2 43 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 257 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 257 (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 45 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 257 (accept_3_2 40 45 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 45 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 257 (accept_3_2 37 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 257 (Polychromatic418967fa.accept_13_9_6_10_1_666 35 45 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 257 (accept_3_2 34 45 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 257 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 45 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 257 (accept_3_2 31 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 45 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 257 (accept_3_2 28 45 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 45 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 257 (accept_3_2 25 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 257 (Polychromatic418967fa.accept_19_5_7_10_1_7375 24 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 45 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 257 (accept_3_2 22 45 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 257 (Polychromatic418967fa.accept_16_5_13_1_1_2084 21 45 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 257 (accept_3_2 19 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 257 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 257 (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 45 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 257 (accept_3_2 16 45 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 45 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 257 (accept_3_2 13 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 257 (Polychromatic418967fa.accept_20_11_5_17_1_5490 11 45 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 257 (accept_3_2 10 45 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 257 (accept_3_2 7 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  257 (Polychromatic418967fa.accept_21_6_3_5_1_8198 6 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 45 257 (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 45 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 257 (accept_3_2 4 45 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 257 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 45 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 257 (accept_3_2 1 45 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  257))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 257 (allA_succ_of_accept 43 44 257 (accept_3_2 43 44
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 257
  (Polychromatic418967fa.accept_9_6_8_5_1_837 42 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 257 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 44 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 257 (accept_3_2 40 44 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 38
  44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 257 (accept_3_2 37 44
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 257
  (Polychromatic418967fa.accept_16_4_12_1_1_1204 36 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 257 (Polychromatic418967fa.accept_14_7_2_5_1_4528 35 44 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 257 (accept_3_2 34 44 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 32
  44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 257 (accept_3_2 31 44
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 257 (Polychromatic418967fa.accept_9_3_8_5_1_65
  30 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 257 (accept_3_2 28 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 257 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 44 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 257 (accept_3_2 25 44 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 44 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 257
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 257 (accept_3_2 22 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  44 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 44 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 44 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 257 (accept_3_2 19 44 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 44 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 257 (accept_3_2 16 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 257 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 44 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 257 (accept_3_2 13 44 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 44 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 44 257 (accept_3_2 10 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  44 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 44 257 (Polychromatic418967fa.accept_13_8_5_10_1_2701 8 44 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 257 (accept_3_2 7 44 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 44 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 257 (accept_3_2 4 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 44 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 257 (accept_3_2 1 44 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 257)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 257 (allA_of_3_0 43 43 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 257 (allA_succ_of_accept 41 42 257
  (Polychromatic418967fa.accept_13_2_3_10_1_658 41 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 257 (accept_3_2 40 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 257 (accept_3_2 37 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 257 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 42 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 257 (accept_3_2 34 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 257 (Polychromatic418967fa.accept_13_7_3_10_1_656 33 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 257 (Polychromatic418967fa.accept_13_6_3_10_1_698 32 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 257 (accept_3_2 31 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 42 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 257 (accept_3_2 28 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 257 (accept_3_2 25 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 42 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 257 (accept_3_2 22 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 257 (accept_3_2 19 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 42 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 257 (accept_3_2 16 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 257 (accept_3_2 13 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 42 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 257 (accept_3_2 10 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 257 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 42 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 257 (accept_3_2 7 42 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 257 (Polychromatic418967fa.accept_13_6_3_10_1_698 6 42 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 257
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 257 (accept_3_2 4 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 42 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 257 (accept_3_2 1 42 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 257)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 257 (allA_succ_of_accept 40 41
  257 (accept_3_2 40 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 257 (Polychromatic418967fa.accept_13_12_2_10_1_2698 38 41 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 257 (accept_3_2 37 41 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 257 (Polychromatic418967fa.accept_15_5_11_2_1_1095
  35 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 257 (accept_3_2 34
  41 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 257
  (Polychromatic418967fa.accept_26_7_15_23_1_15652 33 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 41 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 257 (accept_3_2 31 41 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 257 (Polychromatic418967fa.accept_17_13_7_2_1_4562 30 41 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 257
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 257 (accept_3_2 28 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 257 (Polychromatic418967fa.accept_21_6_20_5_1_12663 27 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 257 (Polychromatic418967fa.accept_10_6_1_7_1_342 26 41 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 257 (accept_3_2 25 41 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 257 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 41 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 257
  (Polychromatic418967fa.accept_11_1_8_4_1_717 23 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 257 (accept_3_2 22 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 257 (Polychromatic418967fa.accept_13_8_2_10_1_652 21 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 257 (Polychromatic418967fa.accept_14_6_13_5_1_534 20 41 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 257 (accept_3_2 19 41 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 41 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 257
  (Polychromatic418967fa.accept_25_17_16_7_1_15651 17 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 41 257 (accept_3_2 16 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 41 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 41 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 257 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 41 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 257 (accept_3_2 13 41 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 257 (Polychromatic418967fa.accept_11_1_8_4_1_717
  12 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 257 (accept_3_2 10 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 257 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 41 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 257 (accept_3_2 7 41 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 257 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 41 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 257
  (Polychromatic418967fa.accept_13_5_2_10_1_248 5 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 257 (accept_3_2 4 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  257 (Polychromatic418967fa.accept_13_3_2_10_1_2697 3 41 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 41 257 (Polychromatic418967fa.accept_16_2_9_1_1_6404 2 41 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 257 (accept_3_2 1 41 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 41 257))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 257 (allA_of_3_0 40 40
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 257 (allA_succ_of_accept 38 39 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 257 (accept_3_2 37 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 39 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 257 (accept_3_2 34 39 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 39 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 257 (accept_3_2 31 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 39 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 257 (accept_3_2 28 39 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 257 (accept_3_2 25 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 39 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 257 (accept_3_2 22 39 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 39 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 257 (accept_3_2 19 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 39 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 257 (accept_3_2 16 39 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 257 (accept_3_2 13 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 39 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 257 (accept_3_2 10 39 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 39 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 257 (accept_3_2 7 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 257 (Polychromatic418967fa.accept_25_5_14_7_1_15650 5 39 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 257 (accept_3_2 4 39 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 257 (Polychromatic418967fa.accept_17_3_5_2_1_14381 3 39 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 257 (accept_3_2 1 39 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 257))))))))))))))))))))))))))))))))))))))) (allB_succ 38 257
  (allA_succ_of_accept 37 38 257 (accept_3_2 37 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 257 (accept_3_2 34 38 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 257
  (Polychromatic418967fa.accept_11_10_5_4_1_711 32 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 257 (accept_3_2 31 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 38 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 257 (accept_3_2 28 38 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 257 (accept_3_2 25 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 257 (accept_3_2 22 38 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 257
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 257 (accept_3_2 19 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 257 (Polychromatic418967fa.accept_16_2_6_1_1_2069 18 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 257 (accept_3_2 16 38 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 257
  (Polychromatic418967fa.accept_21_14_17_5_1_3459 14 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 257 (accept_3_2 13 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 257 (accept_3_2 10 38 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 257 (accept_3_2 7 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  257 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 38 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 257 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 38 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 257 (accept_3_2 4 38 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 38
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 257 (accept_3_2 1 38 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 257)))))))))))))))))))))))))))))))))))))) (allB_succ 37 257
  (allA_of_3_0 37 37 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 257 (allA_succ_of_accept 35 36 257
  (Polychromatic418967fa.accept_16_3_4_1_1_2996 35 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 257 (accept_3_2 34 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 257 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 36 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 257 (accept_3_2 31 36 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 257 (Polychromatic418967fa.accept_16_14_4_1_1_3049 30 36 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 257 (accept_3_2 28 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 257 (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 36 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 257 (accept_3_2 25 36 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 36 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 257
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 257 (accept_3_2 22 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 36 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 257 (accept_3_2 19 36 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 36 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 257 (accept_3_2 16 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 257 (Polychromatic418967fa.accept_19_15_17_10_1_8935 15 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 257 (Polychromatic418967fa.accept_16_14_4_1_1_3049 14 36 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 257 (accept_3_2 13 36 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 257 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 36
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 257 (accept_3_2 10 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 257 (Polychromatic418967fa.accept_21_9_15_5_1_3500 9 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 257 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 36 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 257 (accept_3_2 7 36 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 36 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 257 (accept_3_2 4 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  257 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 257 (Polychromatic418967fa.accept_19_2_17_10_1_4629 2 36 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 257 (accept_3_2 1 36 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 257)))))))))))))))))))))))))))))))))))) (allB_succ 35 257 (allA_succ_of_accept 34 35 257
  (accept_3_2 34 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 257
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 257 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 35 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 257 (accept_3_2 31 35 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 257 (accept_3_2 28 35
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 257
  (Polychromatic418967fa.accept_13_1_9_10_1_625 27 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 257 (accept_3_2 25 35 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 257 (Polychromatic418967fa.accept_10_3_5_7_1_330
  23 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 257 (accept_3_2 22
  35 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 257
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 257 (accept_3_2 19 35 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 257 (Polychromatic418967fa.accept_11_6_2_4_1_1703
  17 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 257 (accept_3_2 16
  35 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 257
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 257 (accept_3_2 13 35 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 257 (accept_3_2 10 35
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 257
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 257 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 35 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 257 (accept_3_2 7 35 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 257 (Polychromatic418967fa.accept_19_5_16_10_1_7384
  5 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 257 (accept_3_2 4 35
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 257 (Polychromatic418967fa.accept_9_3_8_5_1_65
  3 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 257 (accept_3_2 1 35 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  257))))))))))))))))))))))))))))))))))) (allB_succ 34 257 (allA_of_3_0 34 34 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 257 (allA_succ_of_accept 32 33 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 257 (accept_3_2 31 33 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 30
  33 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 257 (accept_3_2 28 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 257 (accept_3_2 25 33 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 257 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 33 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 257
  (Polychromatic418967fa.accept_19_4_14_10_1_7467 23 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 257 (accept_3_2 22 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 257 (accept_3_2 19 33 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 257 (Polychromatic418967fa.accept_17_1_16_2_1_1404 18 33 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 257 (accept_3_2 16 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 257 (accept_3_2 13 33 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 257 (accept_3_2 10 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 257 (Polychromatic418967fa.accept_18_9_15_5_1_6551 9 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 257 (accept_3_2 7 33 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 257 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 33 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 257
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 257 (accept_3_2 4 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  257 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 33 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 257 (accept_3_2 1 33 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 257))))))))))))))))))))))))))))))))) (allB_succ 32 257 (allA_succ_of_accept 31 32 257
  (accept_3_2 31 32 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 32 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 32 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 257 (accept_3_2 28 32 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 257 (Polychromatic418967fa.accept_12_2_8_5_1_408
  26 32 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 257 (accept_3_2 25
  32 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 257
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 32 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 32 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 257 (accept_3_2 22 32 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 20
  32 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 257 (accept_3_2 19 32
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 257
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 32 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 32 257 (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 32 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 257 (accept_3_2 16 32 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 32 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 257 (Polychromatic418967fa.accept_10_4_2_7_1_373
  14 32 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 257 (accept_3_2 13
  32 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 257
  (Polychromatic418967fa.accept_13_12_6_10_1_667 12 32 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 32 257 (Polychromatic418967fa.accept_18_11_14_5_1_3951 11 32 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 257 (accept_3_2 10 32 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 32 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 32
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 257 (accept_3_2 7 32 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6
  32 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 257
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 32 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 257 (accept_3_2 4 32 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 32 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 257 (accept_3_2 1 32 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 257)))))))))))))))))))))))))))))))) (allB_succ 31 257 (allA_of_3_0 31 31 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 257 (allA_succ_of_accept 29 30 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 257 (accept_3_2 28 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 30 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 257 (accept_3_2 25 30 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 30 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 257 (accept_3_2 22 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 257 (Polychromatic418967fa.accept_13_8_4_10_1_4358 21 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 30 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 257 (accept_3_2 19 30 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 30 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 257 (accept_3_2 16 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 257 (Polychromatic418967fa.accept_13_1_4_10_1_622 14 30 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 257 (accept_3_2 13 30 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 257 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 30 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 257 (accept_3_2 10 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 257 (Polychromatic418967fa.accept_18_9_12_5_1_864 9 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 30 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 30 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 257 (accept_3_2 7 30 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 30 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 257
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 257 (accept_3_2 4 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 30 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 257 (accept_3_2 1 30 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 257)))))))))))))))))))))))))))))) (allB_succ 29 257 (allA_succ_of_accept 28 29 257
  (accept_3_2 28 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 29 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 257 (accept_3_2 25 29 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 29 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 257
  (Polychromatic418967fa.accept_17_6_12_2_1_10966 23 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 257 (accept_3_2 22 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 29 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 257 (accept_3_2 19 29 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 29 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 257 (accept_3_2 16 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 257 (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 29 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 257 (accept_3_2 13 29 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 29 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 257 (accept_3_2 10 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 257 (Polychromatic418967fa.accept_16_9_13_1_1_3069 9 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 257 (accept_3_2 7 29 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 29 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 257
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 257 (accept_3_2 4 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  257 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 29 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 2 29 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 257 (accept_3_2 1 29 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 257))))))))))))))))))))))))))))) (allB_succ 28 257 (allA_of_3_0 28 28 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 257 (allA_succ_of_accept 26 27 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 257 (accept_3_2 25 27 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 257 (Polychromatic418967fa.accept_13_11_1_10_1_648
  24 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 257
  (Polychromatic418967fa.accept_19_4_8_10_1_11682 23 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 257 (accept_3_2 22 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 257 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 257 (accept_3_2 19 27 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 257
  (Polychromatic418967fa.accept_13_4_1_10_1_693 17 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 257 (accept_3_2 16 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 257 (accept_3_2 13 27 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 257 (Polychromatic418967fa.accept_16_12_11_1_1_4088 12 27 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 257 (accept_3_2 10 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 257 (accept_3_2 7 27 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 257
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 257 (accept_3_2 4 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  257 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 27 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 27 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 257 (accept_3_2 1 27 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 27 257))))))))))))))))))))))))))) (allB_succ 26 257 (allA_succ_of_accept 25 26 257
  (accept_3_2 25 26 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 257
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 26 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 257 (accept_3_2 22 26 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 20
  26 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 257 (accept_3_2 19 26
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 257
  (Polychromatic418967fa.accept_19_18_7_10_1_9001 18 26 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 257 (Polychromatic418967fa.accept_14_3_12_5_1_153 17 26 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 257 (accept_3_2 16 26 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 257 (Polychromatic418967fa.accept_18_14_8_5_1_860
  14 26 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 257 (accept_3_2 13
  26 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 257
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 26 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 257 (accept_3_2 10 26 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 257 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  26 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 257 (accept_3_2 7 26 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 6
  26 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 257
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 26 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 257 (accept_3_2 4 26 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 26 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 257 (accept_3_2 1 26 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 257)))))))))))))))))))))))))) (allB_succ 25 257 (allA_of_3_0 25 25 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 257 (allA_succ_of_accept 23 24 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 257 (accept_3_2 22 24 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21
  24 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 24 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 257 (accept_3_2 19 24 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 257 (Polychromatic418967fa.accept_19_18_5_10_1_2175 18 24 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 257 (accept_3_2 16 24 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 257
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 14 24 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 257 (accept_3_2 13 24 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 24 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 257 (accept_3_2 10 24 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 24 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 257 (accept_3_2 7 24 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  257 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 24 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 24 257 (Polychromatic418967fa.accept_23_5_1_4_1_13953 5 24 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 257 (accept_3_2 4 24 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 24 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 257 (accept_3_2 1 24 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  257)))))))))))))))))))))))) (allB_succ 23 257 (allA_succ_of_accept 22 23 257 (accept_3_2 22 23 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 257 (Polychromatic418967fa.accept_14_7_9_5_1_529 21 23 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 257
  (Polychromatic418967fa.accept_19_1_4_10_1_12988 20 23 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 257 (accept_3_2 19 23 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 23 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 257 (accept_3_2 16 23 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 23 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 257 (accept_3_2 13 23 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 257 (Polychromatic418967fa.accept_17_12_6_2_1_2346 12 23 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 257 (accept_3_2 10 23 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 257 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 23 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 257
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 23 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 257 (accept_3_2 7 23 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 23 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 257 (accept_3_2 4 23 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 23 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 257 (accept_3_2 1 23 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 257))))))))))))))))))))))) (allB_succ 22 257 (allA_of_3_0 22 22
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 257 (allA_succ_of_accept 20 21 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 257 (accept_3_2 19 21 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 257 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 21 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 21 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 257 (accept_3_2 16 21 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 257 (accept_3_2 13 21 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 21 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 257 (accept_3_2 10 21 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 257 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 21 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 257 (accept_3_2 7 21 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  257 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 257 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 21 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 257 (accept_3_2 4 21 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 257 (accept_3_2 1 21 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 257))))))))))))))))))))) (allB_succ 20 257 (allA_succ_of_accept
  19 20 257 (accept_3_2 19 20 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 20 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 20 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 257 (accept_3_2 16 20 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 257 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 20 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 257 (accept_3_2 13
  20 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 257
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 20 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 20 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 257 (accept_3_2 10 20 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 20
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 257 (accept_3_2 7 20 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  20 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 20 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 257 (accept_3_2 4 20 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 257 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 20 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 257 (accept_3_2 1 20 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 257)))))))))))))))))))) (allB_succ 19 257 (allA_of_3_0 19 19 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 257 (allA_succ_of_accept 17 18 257 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 18 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 257 (accept_3_2 16 18 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  18 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 257
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 18 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 257 (accept_3_2 13 18 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 257 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 18 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 257 (accept_3_2 10 18 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 18 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 257 (accept_3_2 7 18 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 18 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 257 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 18 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 257 (accept_3_2 4 18 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  18 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 257 (accept_3_2 1 18 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 257)))))))))))))))))) (allB_succ 17 257 (allA_succ_of_accept 16
  17 257 (accept_3_2 16 17 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 17 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 257 (Polychromatic418967fa.accept_13_1_4_10_1_622 14 17 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 257 (accept_3_2 13 17 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 17 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  17 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 257 (accept_3_2 10 17
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 257 (Polychromatic418967fa.accept_7_2_3_5_1_34
  9 17 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 17 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 257 (accept_3_2 7 17 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  257 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 17 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 257 (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 17 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 257 (accept_3_2 4 17 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 17 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 17
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 257 (accept_3_2 1 17 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 257))))))))))))))))) (allB_succ 16 257 (allA_of_3_0 16 16 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 257 (allA_succ_of_accept 14 15 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 257 (accept_3_2 13 15 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 15 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 15 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 257 (accept_3_2 10 15 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 15 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 257 (accept_3_2 7 15 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 257 (Polychromatic418967fa.accept_13_5_2_10_1_248 5 15 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 257 (accept_3_2 4 15 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 257 (accept_3_2 1 15 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 257))))))))))))))) (allB_succ 14 257 (allA_succ_of_accept 13 14
  257 (accept_3_2 13 14 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 257
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 14 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 257 (accept_3_2 10 14 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 257 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  14 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 257 (accept_3_2 7 14 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 257 (Polychromatic418967fa.accept_19_6_14_10_1_4624
  6 14 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 257
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 14 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 257 (accept_3_2 4 14 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 14 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 257 (accept_3_2 1 14 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 257)))))))))))))) (allB_succ 13 257 (allA_of_3_0 13 13 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 257 (allA_succ_of_accept 11 12 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 12 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 257 (accept_3_2 10 12 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 257 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9
  12 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 12 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 257 (accept_3_2 7 12 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  257 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 12 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 257 (accept_3_2 4 12 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 257 (Polychromatic418967fa.accept_14_3_12_5_1_153 3 12 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 12
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 257 (accept_3_2 1 12 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 257)))))))))))) (allB_succ 11 257 (allA_succ_of_accept 10 11 257
  (accept_3_2 10 11 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 11 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 11 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 257 (accept_3_2 7 11 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 257 (Polychromatic418967fa.accept_15_5_11_2_1_1095
  5 11 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 257 (accept_3_2 4 11
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 257 (Polychromatic418967fa.accept_9_3_2_5_1_234
  3 11 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 257 (accept_3_2 1 11 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  257))))))))))) (allB_succ 10 257 (allA_of_3_0 10 10 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 257
  (allA_succ_of_accept 8 9 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 257 (accept_3_2 7 9 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 257 (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 9 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 257 (Polychromatic418967fa.accept_16_5_9_1_1_2070 5
  9 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 257 (accept_3_2 4 9 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 9
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 257 (accept_3_2 1 9 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 257)))))))))
  (allB_succ 8 257 (allA_succ_of_accept 7 8 257 (accept_3_2 7 8 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 8 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 257 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 8 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 257 (accept_3_2 4 8 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 8 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 257 (accept_3_2 1 8 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 257))))))))
  (allB_succ 7 257 (allA_of_3_0 7 7 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 257 (allA_succ_of_accept 5
  6 257 (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 6 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 6 257 (accept_3_2 4 6 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 6 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 257 (accept_3_2 1 6 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 257)))))) (allB_succ 5 257 (allA_succ_of_accept 4 5 257 (accept_3_2 4 5
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 257 (Polychromatic418967fa.accept_10_3_5_7_1_330
  3 5 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 257
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 2 5 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 257 (accept_3_2 1 5 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 257)))))
  (allB_succ 4 257 (allA_of_3_0 4 4 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 257 (allA_succ_of_accept 2
  3 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 257 (accept_3_2 1 3 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 257)))
  (allB_succ 2 257 (allA_succ_of_accept 1 2 257 (accept_3_2 1 2 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  257)) (allB_two
  257)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


