-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch265_Segment000
-- name    : Polychromatic418967fa_Branch265_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:47:13.404661+00:00
-- url     : https://prove2.me/theorems/ddd95394-8e04-4196-85d1-df536e0a4b30
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

def Polychromatic418967fa.branch_265_segment_000 : allB 123 265 :=
  allB_succ 122 265 (allA_of_3_1 122 122 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 121 265
  (allA_succ_of_accept 120 121 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 120 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 265 (accept_3_3 119 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 121 265 (Polychromatic418967fa.accept_13_1_4_5_1_113 118 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 265
  (Polychromatic418967fa.accept_17_15_2_10_1_9021 117 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 121 265 (accept_3_3 116 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 121 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 115 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 121 265 (Polychromatic418967fa.accept_10_4_1_5_1_1018 114 121
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 265 (accept_3_3 113 121
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 265
  (Polychromatic418967fa.accept_15_7_1_10_1_305 112 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 121 265 (Polychromatic418967fa.accept_15_6_1_10_1_1549 111 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 121 265 (accept_3_3 110 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 109 121 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 109 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 121 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 108 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 121 265 (accept_3_3 107 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 121 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 106 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 121 265 (Polychromatic418967fa.accept_13_1_4_5_1_113 105 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 121 265 (accept_3_3 104 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 121 265 (Polychromatic418967fa.accept_13_12_4_5_1_1637 103
  121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 121 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 102 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 121 265 (accept_3_3 101 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 121 265 (Polychromatic418967fa.accept_13_9_4_5_1_1651 100 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 121 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 121 265 (accept_3_3 98 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 121 265 (Polychromatic418967fa.accept_13_6_4_5_1_2330 97 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 121 265
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 96 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 121 265 (accept_3_3 95 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 121 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 94 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 121 265 (Polychromatic418967fa.accept_13_2_4_5_1_3152 93 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 121 265 (accept_3_3 92 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 121 265 (Polychromatic418967fa.accept_19_15_7_18_1_9532 91 121
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 121 265
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 90 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 121 265 (accept_3_3 89 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 121 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 121 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 121 265 (accept_3_3 86 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 121 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 85 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 121 265
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 84 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 121 265 (accept_3_3 83 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 121 265 (Polychromatic418967fa.accept_15_7_1_10_1_305 82 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 121 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 121 265 (accept_3_3 80 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 121 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 79 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 121 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 121 265 (accept_3_3 77 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 121 265 (Polychromatic418967fa.accept_10_6_1_5_1_1024 76 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 121 265 (Polychromatic418967fa.accept_13_10_4_5_1_2331 75 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 121 265 (accept_3_3 74 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 121 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 121 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 121 265
  (Polychromatic418967fa.accept_19_15_7_18_1_9532 72 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 121 265 (accept_3_3 71 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 121 265 (Polychromatic418967fa.accept_20_10_1_5_1_7745 70 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 69 121
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 121 265 (accept_3_3 68 121
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 121 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 121 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 265 (accept_3_3 65 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 121 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 265
  (Polychromatic418967fa.accept_17_12_2_10_1_2862 63 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 121 265 (accept_3_3 62 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 121 265 (Polychromatic418967fa.accept_13_9_4_5_1_1651 61 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 121 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 265 (accept_3_3 59 121 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 265 (Polychromatic418967fa.accept_13_6_4_5_1_2330
  58 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 265 (accept_3_3 56 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 265 (Polychromatic418967fa.accept_19_17_7_18_1_6629 55 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 265 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 265 (accept_3_3 53 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 121 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 265
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 51 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 265 (accept_3_3 50 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 265 (Polychromatic418967fa.accept_13_9_4_5_1_1651 48 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 265 (accept_3_3 47 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 121 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 265 (accept_3_3 44 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 265 (Polychromatic418967fa.accept_17_8_2_10_1_2879 42 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 265 (accept_3_3 41 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 265 (Polychromatic418967fa.accept_13_1_4_5_1_113 40 121
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 265 (accept_3_3 38 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 265 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 265 (accept_3_3 35 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 265 (Polychromatic418967fa.accept_10_4_1_5_1_1018 34 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 265
  (Polychromatic418967fa.accept_19_14_7_18_1_12160 33 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 121 265 (accept_3_3 32 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 121 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 265 (Polychromatic418967fa.accept_19_11_7_18_1_5284 30 121
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 265 (accept_3_3 29 121
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 265
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 28 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 121 265 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 265 (accept_3_3 26 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 121 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 24
  121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 265 (accept_3_3 23
  121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 121 265 (Polychromatic418967fa.accept_15_6_1_10_1_1549 21 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 265 (accept_3_3 20 121 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 121 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 265 (accept_3_3 17 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 265 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 265 (accept_3_3 14 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 121 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 265
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 265 (accept_3_3 11 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 265 (accept_3_3 8 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 265 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 265
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 265 (accept_3_3 5 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 121 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 265 (accept_3_3 2 121 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 121 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 265 (allA_succ_of_accept 119 120 265 (accept_3_3 119 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 120 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 118 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 120 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 117 120
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 265 (accept_3_3 116 120
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 115 120 265 5 23 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 114 120 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 114 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 120 265 (accept_3_3 113 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 120 265 (Polychromatic418967fa.accept_11_2_10_1_1_1017 112 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 265 (Polychromatic418967fa.accept_16_15_8_9_1_2563 111 120 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 120 265 5 22 24 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 265
  (Polychromatic418967fa.accept_9_1_3_4_1_47 109 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 120 265 (Polychromatic418967fa.accept_11_9_10_1_1_581 108 120 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 265 (accept_3_3 107 120 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 106 120 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 120 265 5 21 24 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 120 265 (accept_3_3 104 120 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 120 265 (Polychromatic418967fa.accept_7_5_1_6_1_163
  103 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 120 265
  (Polychromatic418967fa.accept_13_11_3_5_1_982 102 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 120 265 (accept_3_3 101 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  100 120 265 5 20 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 99 120 265 (Polychromatic418967fa.accept_13_8_3_5_1_1636 99 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 120 265 (accept_3_3 98 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 120 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 97 120 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 120 265 (Polychromatic418967fa.accept_7_5_1_6_1_163
  96 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 120 265 5 19 24 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 120 265
  (Polychromatic418967fa.accept_17_9_1_10_1_2859 94 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 120 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 265 (accept_3_3 92 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 120 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 120 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 120 265 5 18 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 120 265 (accept_3_3 89 120 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 120 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 120 265 (accept_3_3 86 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  120 265 5 17 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 120 265 (Polychromatic418967fa.accept_13_6_3_5_1_3167 84 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 120 265 (accept_3_3 83 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 120 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 120 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 265 (Polychromatic418967fa.accept_16_1_8_9_1_3462
  81 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 120 265 5 16 24 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 120 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 120 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 265 (accept_3_3 77 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 120 265 (Polychromatic418967fa.accept_13_11_3_5_1_982 76 120 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 120 265 5 15 24 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 120 265 (accept_3_3 74 120 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 120 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 73
  120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 120 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 120 265 (accept_3_3 71 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  120 265 5 14 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 120 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 265 (accept_3_3 68 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 120 265 (Polychromatic418967fa.accept_13_2_3_5_1_2294 67 120 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 120 265
  (Polychromatic418967fa.accept_13_1_3_5_1_140 66 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 120 265 5 13 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 120 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 120 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 265 (Polychromatic418967fa.accept_13_11_3_5_1_982
  63 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 265 (accept_3_3 62
  120 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 265 5 12 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 265 (accept_3_3 59 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 120 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 265 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 120
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 265 (accept_3_3 56 120
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 120 265 5 11 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 120 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 120 265 (accept_3_3 53 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 120 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 120 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 120 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 265 5 10 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 265
  (Polychromatic418967fa.accept_14_7_8_13_1_3161 49 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 120 265 (Polychromatic418967fa.accept_13_9_3_5_1_1605 48 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 265 (accept_3_3 47 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 120 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 120 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 120 265 5 9 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 120 265 (accept_3_3 44 120 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 120 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 120 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 120 265 (accept_3_3 41 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  120 265 5 8 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 120 265 (Polychromatic418967fa.accept_16_7_8_9_1_9427 39 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 120 265 (accept_3_3 38 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 265 (Polychromatic418967fa.accept_16_4_8_9_1_4639 36 120
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 120 265 5 7 24 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 120 265
  (Polychromatic418967fa.accept_9_7_3_4_1_218 34 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 120 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 265 (accept_3_3 32 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 120 265 (Polychromatic418967fa.accept_11_9_10_1_1_581 31 120 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 265 5 6 24 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 265 (accept_3_3 29 120 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 28
  120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 265
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 120 265 (accept_3_3 26 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  120 265 5 5 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 120 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 120 265 (accept_3_3 23 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 120 265 (Polychromatic418967fa.accept_13_9_3_5_1_1605 22 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 265 (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 120
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 265 5 4 24 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 120 265 (Polychromatic418967fa.accept_21_18_15_13_1_4130 18 120 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 265 (accept_3_3 17 120 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 120 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 265 5 3 24 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 265 (accept_3_3 14 120 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 265
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 120 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 265 (accept_3_3 11 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 120 265 5 2 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 120 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 120 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 265 (accept_3_3 8 120 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 120 265 5 1 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 120 265 (Polychromatic418967fa.accept_16_4_8_9_1_4639 4 120 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 265 (Polychromatic418967fa.accept_18_3_12_13_1_3307 3 120
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 265 (accept_3_3 2 120 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 1
  120 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 265 (allA_of_3_1 119 119 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 118 265
  (allA_succ_of_accept 117 118 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 117 118 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 118 265 (accept_3_3 116 118 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 115 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 118 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 114 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 118 265 (accept_3_3 113 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 118 265 (Polychromatic418967fa.accept_10_2_8_5_1_587 112 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 118 265 (accept_3_3 110 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 118 265 (Polychromatic418967fa.accept_15_4_13_10_1_1508 109
  118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 118 265
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 108 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 118 265 (accept_3_3 107 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 118 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 106 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 118 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 118 265 (accept_3_3 104 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 118 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 102 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 118 265 (accept_3_3 101 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 118 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 100 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 118 265 (accept_3_3 98 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 118 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 118 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 96 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 118 265 (accept_3_3 95 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 118 265 (Polychromatic418967fa.accept_13_3_1_5_1_499 94 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 118 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 118 265 (accept_3_3 92 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 118 265
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 90 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 118 265 (accept_3_3 89 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 118 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 118 265 (accept_3_3 86 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 118 265 (Polychromatic418967fa.accept_24_13_22_1_1_16203 85 118 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 118 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 118 265 (accept_3_3 83 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 118 265 (Polychromatic418967fa.accept_10_2_8_5_1_587 82 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 118 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 118 265 (accept_3_3 80 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 118 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 78 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 118 265 (accept_3_3 77 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 118 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 76 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 265 (accept_3_3 74 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 265 (Polychromatic418967fa.accept_10_3_8_5_1_606 73 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 265
  (Polychromatic418967fa.accept_10_2_8_5_1_587 72 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 118 265 (accept_3_3 71 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 118 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 118 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 265 (accept_3_3 68 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 265 (accept_3_3 65 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 265 (accept_3_3 62 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 265 (accept_3_3 59 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 265 (Polychromatic418967fa.accept_13_6_1_5_1_3988 58 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 265 (accept_3_3 56 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 265
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 54 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 118 265 (accept_3_3 53 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 118 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 118 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 118 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 265 (accept_3_3 50 118 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 265
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 49 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 118 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 118 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 118 265 (accept_3_3 47 118 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 118 265 (Polychromatic418967fa.accept_15_1_13_10_1_1507 46 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 118 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 118 265 (accept_3_3 44 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 118 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 118 265 (accept_3_3 41 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 118 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 118 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 118 265 (accept_3_3 38 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 118 265 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 118 265 (Polychromatic418967fa.accept_19_17_4_18_1_6643 36 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 118 265 (accept_3_3 35 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 118 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 118 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 118 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 118 265 (accept_3_3 32 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 118 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 118 265 (accept_3_3 29 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 118 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 118 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 118 265 (accept_3_3 26 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 118 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 118 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 118 265 (accept_3_3 23 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 118 265 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 118 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 118 265 (accept_3_3 20 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 118 265 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 265 (accept_3_3 17 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 118 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 118 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 118 265 (accept_3_3 14 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 118 265 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 118 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 265 (accept_3_3 11 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 265 (Polychromatic418967fa.accept_20_10_18_5_1_11942 10 118 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 118 265 (accept_3_3 8 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  118 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 118 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 265 (accept_3_3 5 118 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 265 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 118 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 118 265 (accept_3_3 2 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  118 265 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 118 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 118
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 265 (allA_succ_of_accept 116 117 265 (accept_3_3 116 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 265 (Polychromatic418967fa.accept_20_15_17_5_1_6040 115 117 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 265
  (Polychromatic418967fa.accept_15_9_12_10_1_809 114 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 117 265 (accept_3_3 113 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 112 117 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 117 265 (Polychromatic418967fa.accept_12_3_9_1_1_290 111 117
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 265 (accept_3_3 110 117
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 109 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 117 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 108 117 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 265 (accept_3_3 107 117 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 106 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 117 265
  (Polychromatic418967fa.accept_11_6_7_1_1_564 105 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 117 265 (accept_3_3 104 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 117 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 103 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 117 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 102 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 265 (accept_3_3 101 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 117
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 117 265
  (Polychromatic418967fa.accept_7_1_5_6_1_59 99 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 117 265 (accept_3_3 98 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 117 265 (Polychromatic418967fa.accept_15_7_12_10_1_4335 97 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 117 265 (Polychromatic418967fa.accept_15_6_12_10_1_1543 96 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 265 (accept_3_3 95 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 117 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 265
  (Polychromatic418967fa.accept_10_3_7_5_1_288 93 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 117 265 (accept_3_3 92 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 117 265 (Polychromatic418967fa.accept_16_11_5_9_1_1617 91 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 117 265 (Polychromatic418967fa.accept_14_6_5_13_1_367 90 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 265 (accept_3_3 89 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 117 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 87 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 117 265 (accept_3_3 86 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 117 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 117 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 117 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 265 (accept_3_3 83 117 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 81 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 117 265 (accept_3_3 80 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 117 265 (Polychromatic418967fa.accept_23_10_2_12_1_11407 79 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 265 (accept_3_3 77 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 117 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 117 265 (accept_3_3 74 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 117 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 73 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 117 265 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 265 (accept_3_3 71 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 117 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 265
  (Polychromatic418967fa.accept_15_9_12_10_1_809 69 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 117 265 (accept_3_3 68 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 117 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 117 265 (Polychromatic418967fa.accept_15_6_12_10_1_1543 66 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 265 (accept_3_3 65 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 117 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 265
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 117 265 (accept_3_3 62 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 117 265 (Polychromatic418967fa.accept_11_6_7_1_1_564 61 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 117 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 117 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 265 (accept_3_3 59 117 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 265
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 117 265 (accept_3_3 56 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 117 265 (Polychromatic418967fa.accept_17_4_15_10_1_5139 55 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 117 265 (Polychromatic418967fa.accept_15_9_12_10_1_809 54 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 265 (accept_3_3 53 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 117 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 117 265 (accept_3_3 50 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 117 265 (Polychromatic418967fa.accept_16_1_5_9_1_1649 49 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 117 265 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 265 (accept_3_3 47 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 117 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 265
  (Polychromatic418967fa.accept_16_13_5_9_1_4682 45 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 117 265 (accept_3_3 44 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 117 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 117 265 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 265 (accept_3_3 41 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 117 265 (accept_3_3 38 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 117 265 (Polychromatic418967fa.accept_15_7_12_10_1_4335 37 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 117 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 117 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 265 (accept_3_3 35 117 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 265
  (Polychromatic418967fa.accept_10_3_7_5_1_288 33 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 117 265 (accept_3_3 32 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 117 265 (Polychromatic418967fa.accept_20_11_17_5_1_13413 31 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 265 (Polychromatic418967fa.accept_16_14_5_9_1_5901 30 117 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 265 (accept_3_3 29 117 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 117 265 (accept_3_3 26 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 117 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 117 265 (Polychromatic418967fa.accept_15_9_12_10_1_809 24 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 265 (accept_3_3 23 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 117 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 265
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 265 (accept_3_3 20 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 265 (Polychromatic418967fa.accept_17_2_15_10_1_5171 19 117 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 265 (Polychromatic418967fa.accept_7_4_5_6_1_344
  18 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 265 (accept_3_3 17
  117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 265
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 117 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 117 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 265 (accept_3_3 14 117 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 117 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 265
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 265 (accept_3_3 11 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 265 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 265 (accept_3_3 8 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 265 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 117
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 265
  (Polychromatic418967fa.accept_11_6_7_1_1_564 6 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 265 (accept_3_3 5 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 117 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 265 (accept_3_3 2 117 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 117 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 265 (allA_of_3_1 116 116 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 265
  (allA_succ_of_accept 114 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 114 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 265 (accept_3_3 113 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 115 265 (Polychromatic418967fa.accept_18_4_7_13_1_3303 112 115 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 111 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 115 265 5 22 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 115 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 109 115 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 115 265
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 108 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 115 265 (accept_3_3 107 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 106 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 115 265 5 21 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 115 265 (accept_3_3 104 115 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 115 265 (Polychromatic418967fa.accept_16_7_3_9_1_2557 103 115 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 115 265 (accept_3_3 101 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  100 115 265 5 20 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 99 115 265 (Polychromatic418967fa.accept_17_14_13_10_1_3936 99 115 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 115 265 (accept_3_3 98 115 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 115 265 (Polychromatic418967fa.accept_13_6_11_5_1_133 97 115 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 115 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 96 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 95 115 265 5 19 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 94 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 115 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 93
  115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 115 265 (accept_3_3 92
  115 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 115 265
  (Polychromatic418967fa.accept_9_1_7_4_1_52 91 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 115 265 5 18 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 115 265 (accept_3_3 89 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 115 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 88 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 87 115 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 115 265 (accept_3_3 86 115 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 115 265 5 17 23 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 115 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 115 265 (accept_3_3 83 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 115 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 115 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 115 265 5 16 23 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 115 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 265 (accept_3_3 77 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 115 265 (Polychromatic418967fa.accept_16_12_3_9_1_5886 76 115 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 115 265 5 15 23 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 115 265 (accept_3_3 74 115 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 73
  115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 115 265 (accept_3_3 71 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  115 265 5 14 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 115 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 265 (accept_3_3 68 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 115 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 115 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 66
  115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 115 265 5 13 23 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 115 265
  (Polychromatic418967fa.accept_9_1_7_4_1_52 64 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 115 265 (Polychromatic418967fa.accept_19_6_1_18_1_13556 63 115 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 265 (accept_3_3 62 115 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 265 (Polychromatic418967fa.accept_11_6_5_1_1_586 61 115 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 115 265 5 12 23 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 115 265 (accept_3_3 59 115 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 58
  115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 57 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 265 (accept_3_3 56 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  115 265 5 11 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 265 (accept_3_3 53 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 115 265 (Polychromatic418967fa.accept_14_10_3_13_1_1530 52 115 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 115 265 5 10 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 115 265 (Polychromatic418967fa.accept_19_11_1_18_1_5276 49 115 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 265 (accept_3_3 47 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 115 265 5 9 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 115 265 (accept_3_3 44 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 115 265 (Polychromatic418967fa.accept_17_9_13_10_1_1825 43 115 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 265 (accept_3_3 41
  115 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 115 265 5 8 23 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 115 265
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 265 (accept_3_3 38 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 265 (Polychromatic418967fa.accept_19_17_1_18_1_2693 36 115 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 115 265 5 7 23 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 115 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 115 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 265 (accept_3_3 32 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 115 265 (Polychromatic418967fa.accept_17_14_13_10_1_3936 31 115 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 115 265 5 6 23 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 115 265 (accept_3_3 29 115 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 28
  115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 265
  (Polychromatic418967fa.accept_19_8_1_18_1_5240 27 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 265 (accept_3_3 26 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  115 265 5 5 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 115 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 115 265 (accept_3_3 23 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 115 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 115 265 5 4 23 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 265
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 265 (accept_3_3 17 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 115 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 115 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 265 5 3 23 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 265 (accept_3_3 14 115 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 265 (Polychromatic418967fa.accept_19_13_1_18_1_5279 13 115
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 265 (accept_3_3 11 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  115 265 5 2 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 115 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 115 265 (accept_3_3 8 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 115 265 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 115 265 5 1 23 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 115 265
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 115 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 115 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 265 (accept_3_3 2 115 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 115 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 115 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 265 (allA_succ_of_accept 113 114 265 (accept_3_3 113 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 114 265 (Polychromatic418967fa.accept_13_8_10_5_1_977 112 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50
  111 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 265 (accept_3_3
  110 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 114 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 109 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 114 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 108 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 265 (accept_3_3 107 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 114 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 106 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 265
  (Polychromatic418967fa.accept_23_13_22_12_1_11395 105 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 114 265 (accept_3_3 104 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 114 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 102 114
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 265 (accept_3_3 101 114
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 265
  (Polychromatic418967fa.accept_9_1_6_4_1_49 100 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 114 265 (accept_3_3 98 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 114 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 97 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 114 265 (Polychromatic418967fa.accept_10_6_4_5_1_615
  96 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 265 (accept_3_3 95
  114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 94 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 114 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 265 (accept_3_3 92 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 114 265
  (Polychromatic418967fa.accept_17_5_12_10_1_3963 90 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 114 265 (accept_3_3 89 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 114 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 114 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 265 (accept_3_3 86 114 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 114 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 85
  114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 114 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 114 265 (accept_3_3 83 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 114 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 114 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 265 (accept_3_3 80 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 114 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 114 265 (accept_3_3 77 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 114 265 (Polychromatic418967fa.accept_10_6_4_5_1_615 76 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 265 (accept_3_3 74 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 114 265
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 72 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 114 265 (accept_3_3 71 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 114 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 265 (Polychromatic418967fa.accept_10_9_4_5_1_616 69 114
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 265 (accept_3_3 68 114
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 67 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 114 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 114 265 (accept_3_3 65 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 114 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 63
  114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 265 (accept_3_3 62
  114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 265
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 114 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 114 265 (accept_3_3 59 114 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 114 265 (Polychromatic418967fa.accept_13_6_10_5_1_1648 58 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 114 265 (accept_3_3 56 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 114 265 (Polychromatic418967fa.accept_13_2_10_5_1_1643 54 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 265 (accept_3_3 53 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 114 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 114 265 (accept_3_3 50 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 114 265 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 114 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 265 (accept_3_3 47 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 114 265 (accept_3_3 44 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 114 265 (Polychromatic418967fa.accept_15_12_9_10_1_2326 42 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 265 (accept_3_3 41 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 265 (Polychromatic418967fa.accept_17_6_12_10_1_7781 40 114
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 114 265 (accept_3_3 38 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 114 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 114 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 265 (accept_3_3 35 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 265
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 114 265 (accept_3_3 32 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 114 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 265 (accept_3_3 29 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 114 265 (accept_3_3 26 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 114 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 114 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 265 (accept_3_3 23 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 114 265 (accept_3_3 20 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 114 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 265 (accept_3_3 17 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 114 265 (accept_3_3 14 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 114 265 (Polychromatic418967fa.accept_22_13_4_1_1_6753 13 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 114 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 265 (accept_3_3 11 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 265
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 114 265 (accept_3_3 8 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  114 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 114 265 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 265 (accept_3_3 5 114 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 114 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 114 265 (accept_3_3 2 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  114 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 114 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 114
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 265 (allA_of_3_1 113 113 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 265
  (allA_succ_of_accept 111 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 112 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 112 265 (accept_3_3 110 112 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 112 265 (Polychromatic418967fa.accept_11_10_2_1_1_1036 109 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 112 265
  (Polychromatic418967fa.accept_10_8_2_5_1_596 108 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 112 265 (accept_3_3 107 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 112 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 106 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 112 265 (accept_3_3 104 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 112 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 103 112
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 112 265
  (Polychromatic418967fa.accept_11_3_2_1_1_994 102 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 112 265 (accept_3_3 101 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 112 265 (Polychromatic418967fa.accept_18_10_4_13_1_3296 100 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 112 265 (accept_3_3 98 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 112 265 (Polychromatic418967fa.accept_10_7_2_5_1_298 97 112
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 112 265
  (Polychromatic418967fa.accept_19_1_17_18_1_8101 96 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 112 265 (accept_3_3 95 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 112 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 94 112 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 112 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 112 265 (accept_3_3 92 112 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 112 265 (Polychromatic418967fa.accept_11_3_2_1_1_994
  91 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 112 265
  (Polychromatic418967fa.accept_13_12_8_5_1_976 90 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 112 265 (accept_3_3 89 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 112 265 (Polychromatic418967fa.accept_10_8_2_5_1_596 88 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 112 265 (accept_3_3 86 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 112 265 (Polychromatic418967fa.accept_31_23_19_17_1_16202 85 112 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 112 265
  (Polychromatic418967fa.accept_22_18_2_1_1_6765 84 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 112 265 (accept_3_3 83 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 112 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 82 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 112 265 (accept_3_3 80 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 112 265 (Polychromatic418967fa.accept_13_1_8_5_1_2315 79 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 112 265
  (Polychromatic418967fa.accept_10_8_2_5_1_596 78 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 112 265 (accept_3_3 77 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 112 265 (Polychromatic418967fa.accept_11_10_2_1_1_1036 76 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 112 265 (accept_3_3 74 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 112 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 73 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 112 265
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 72 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 112 265 (accept_3_3 71 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 112 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 112 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 112 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 112 265 (accept_3_3 68 112 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 112 265 (Polychromatic418967fa.accept_10_7_2_5_1_298
  67 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 112 265
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 66 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 112 265 (accept_3_3 65 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 112 265 (Polychromatic418967fa.accept_13_12_8_5_1_976 64 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 112 265 (accept_3_3 62 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 112 265 (Polychromatic418967fa.accept_15_1_7_10_1_287 61 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 112 265
  (Polychromatic418967fa.accept_21_18_7_13_1_8801 60 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 112 265 (accept_3_3 59 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 112 265 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 112 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 112 265 (accept_3_3 56 112 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 112 265 (Polychromatic418967fa.accept_13_3_8_5_1_974
  55 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 112 265
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 112 265 (accept_3_3 53 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 112 265 (Polychromatic418967fa.accept_21_10_7_13_1_10408 52 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 112 265 (accept_3_3 50 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 112 265 (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 112
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 112 265
  (Polychromatic418967fa.accept_10_8_2_5_1_596 48 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 112 265 (accept_3_3 47 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 112 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 112 265 (accept_3_3 44 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 112 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 43 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 112 265
  (Polychromatic418967fa.accept_13_3_8_5_1_974 42 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 112 265 (accept_3_3 41 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 112 265 (Polychromatic418967fa.accept_13_1_8_5_1_2315 40 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 112 265 (accept_3_3 38 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 112 265 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 265
  (Polychromatic418967fa.accept_11_3_2_1_1_994 36 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 112 265 (accept_3_3 35 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 112 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 112 265 (accept_3_3 32 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 112 265 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 112 265
  (Polychromatic418967fa.accept_19_11_17_18_1_5236 30 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 112 265 (accept_3_3 29 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 112 265 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 112 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 265 (accept_3_3 26 112 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 112 265 (Polychromatic418967fa.accept_11_3_2_1_1_994
  25 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 112 265
  (Polychromatic418967fa.accept_19_5_17_18_1_2686 24 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 112 265 (accept_3_3 23 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 112 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 112 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 112 265 (accept_3_3 20 112 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 112 265 (Polychromatic418967fa.accept_15_4_7_10_1_807
  19 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 265
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 112 265 (accept_3_3 17 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 112 265 (Polychromatic418967fa.accept_13_3_8_5_1_974 16 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 265 (accept_3_3 14 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 112 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 265
  (Polychromatic418967fa.accept_13_12_8_5_1_976 12 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 112 265 (accept_3_3 11 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 112 265 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 265 (accept_3_3 8 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 265 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 265
  (Polychromatic418967fa.accept_19_6_17_18_1_8117 6 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 265 (accept_3_3 5 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 265 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 112 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 265 (accept_3_3 2 112 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 265 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1 112 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 265 (allA_succ_of_accept 110 111 265 (accept_3_3 110 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 109 111 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 265 (Polychromatic418967fa.accept_15_3_6_10_1_1539 108
  111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 265 (accept_3_3 107
  111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 106 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 111 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 105 111 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 265 (accept_3_3 104 111 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 111 265 (Polychromatic418967fa.accept_13_12_7_5_1_3147 103 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 111 265 (accept_3_3 101 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 111 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 111 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 99 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 265 (accept_3_3 98 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 97 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 96 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 111 265 (accept_3_3 95 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 111 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 111 265 (Polychromatic418967fa.accept_12_9_3_1_1_303 93 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 265 (accept_3_3 92 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 90 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 111 265 (accept_3_3 89 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 111 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 111 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 111 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 265 (accept_3_3 86 111 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 265 (Polychromatic418967fa.accept_19_9_16_18_1_3887 85 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 265
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 84 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 265 (accept_3_3 83 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 111 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 111 265 (Polychromatic418967fa.accept_12_9_3_1_1_303 81 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 265 (accept_3_3 80 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 265 (accept_3_3 77 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 265 (Polychromatic418967fa.accept_20_15_11_5_1_7737 75 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 265 (accept_3_3 74 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 265
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 72 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 111 265 (accept_3_3 71 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 111 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 265 (accept_3_3 68 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 265 (Polychromatic418967fa.accept_13_2_7_5_1_3189
  67 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 265 (accept_3_3 65 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 265 (Polychromatic418967fa.accept_13_11_7_5_1_2314 63 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 265 (accept_3_3 62 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 265 (accept_3_3 59 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 265 (Polychromatic418967fa.accept_12_9_3_1_1_303 57 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 265 (accept_3_3 56 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 265 (accept_3_3 53 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 111 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 265 (accept_3_3 50 111 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 265
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 48 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 265 (accept_3_3 47 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 265 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 265 (accept_3_3 44 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 265 (accept_3_3 41 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 265 (accept_3_3 38 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 265
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 265 (accept_3_3 35 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 111 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 265 (accept_3_3 32 111 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 265 (Polychromatic418967fa.accept_15_1_6_10_1_23 31 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 265 (accept_3_3 29 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 265 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 265 (accept_3_3 26 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 265 (accept_3_3 23 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 265 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 265 (accept_3_3 20 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 265 (accept_3_3 17 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 111 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 265 (accept_3_3 14 111 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 265 (Polychromatic418967fa.accept_17_13_9_10_1_2888 13 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 265
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 265 (accept_3_3 11 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 111 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 265 (accept_3_3 8 111 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 265 (accept_3_3 5 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 265 (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 265 (accept_3_3 2 111 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 111 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 265 (allA_of_3_1 110 110 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 265
  (allA_succ_of_accept 108 109 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 108 109 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 265 (accept_3_3 107 109 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 109 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 106 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 105 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 265 (accept_3_3 104 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 103 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 102 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 265 (accept_3_3 101 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 100 109
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 265
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 99 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 265 (accept_3_3 98 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 265 (accept_3_3 95 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 94 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 265
  (Polychromatic418967fa.accept_7_2_4_6_1_166 93 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 265 (accept_3_3 92 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 265 (Polychromatic418967fa.accept_10_1_9_5_1_83 91 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 265 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 265 (accept_3_3 89 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 109 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 265
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 265 (accept_3_3 86 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 265 (Polychromatic418967fa.accept_16_5_13_9_1_2594 85 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 265 (accept_3_3 83 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 265
  (Polychromatic418967fa.accept_10_1_9_5_1_83 81 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 265 (accept_3_3 80 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 265 (accept_3_3 77 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 76 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 265 (accept_3_3 74 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 265 (accept_3_3 71 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 69 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 265 (accept_3_3 68 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 265 (Polychromatic418967fa.accept_15_7_4_10_1_1513 67 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 265 (accept_3_3 65 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 265 (Polychromatic418967fa.accept_10_4_9_5_1_84 64 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 265
  (Polychromatic418967fa.accept_25_13_9_15_1_16201 63 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 109 265 (accept_3_3 62 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 109 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 109 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 109 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 265 (accept_3_3 59 109 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 265 (Polychromatic418967fa.accept_7_2_4_6_1_166
  58 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 265 (accept_3_3 56 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 265 (Polychromatic418967fa.accept_16_7_13_9_1_1653 55 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 265 (accept_3_3 53 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 265
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 265 (accept_3_3 50 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 265 (Polychromatic418967fa.accept_16_1_13_9_1_2551 49 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 265 (accept_3_3 47 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 265 (Polychromatic418967fa.accept_10_6_9_5_1_1046 46 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 265
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 265 (accept_3_3 44 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 265 (accept_3_3 41 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 265 (accept_3_3 38 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 265 (accept_3_3 35 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 265 (accept_3_3 32 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 265 (accept_3_3 29 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 265
  (Polychromatic418967fa.accept_20_7_9_5_1_292 27 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 265 (accept_3_3 26 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 265 (accept_3_3 23 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 265 (Polychromatic418967fa.accept_15_7_4_10_1_1513 22 109 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 265 (accept_3_3 20 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 265 (Polychromatic418967fa.accept_17_1_7_10_1_1835 18 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 265 (accept_3_3 17 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 109 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 265 (accept_3_3 14 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 265 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 265 (accept_3_3 11 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 265
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 265 (accept_3_3 8 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 265 (accept_3_3 5 109 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 109 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 265
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 265 (accept_3_3 2 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 265 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 109 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 265 (allA_succ_of_accept 107 108 265 (accept_3_3 107 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 108 265 (Polychromatic418967fa.accept_13_2_4_5_1_3152 106 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 265 (Polychromatic418967fa.accept_13_1_4_5_1_113
  105 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 265 (accept_3_3
  104 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 108 265
  (Polychromatic418967fa.accept_10_3_8_5_1_606 103 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 108 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 102 108 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 265 (accept_3_3 101 108 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 108 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 100 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 265
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 99 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 108 265 (accept_3_3 98 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 108 265 (Polychromatic418967fa.accept_10_7_8_5_1_1008 97 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 108 265 (Polychromatic418967fa.accept_15_6_3_10_1_2341 96 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 108 265 (accept_3_3 95 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 265 (Polychromatic418967fa.accept_20_14_8_5_1_6090 94 108
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 93 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 108 265 (accept_3_3 92 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 108 265 (Polychromatic418967fa.accept_22_3_20_1_1_16200 91 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 108 265 (Polychromatic418967fa.accept_13_12_4_5_1_1637 90 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 108 265 (accept_3_3 89 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 88 108 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 265
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 87 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 108 265 (accept_3_3 86 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 108 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 85 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 108 265 (Polychromatic418967fa.accept_13_6_4_5_1_2330 84 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 265 (accept_3_3 83 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 265 (Polychromatic418967fa.accept_10_2_8_5_1_587 82 108
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 265
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 108 265 (accept_3_3 80 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 108 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 108 265 (Polychromatic418967fa.accept_22_12_20_1_1_6721 78 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 265 (accept_3_3 77 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 265 (Polychromatic418967fa.accept_11_10_9_1_1_2186 76 108
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 265
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 75 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 108 265 (accept_3_3 74 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 108 265 (Polychromatic418967fa.accept_10_3_8_5_1_606 73 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 108 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 265 (accept_3_3 71 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 265 (Polychromatic418967fa.accept_20_10_8_5_1_7735 70 108 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 265
  (Polychromatic418967fa.accept_8_5_4_1_1_111 69 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 108 265 (accept_3_3 68 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 108 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 108 265 (Polychromatic418967fa.accept_13_1_4_5_1_113 66 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 108 265 (accept_3_3 65 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 265 (Polychromatic418967fa.accept_13_12_4_5_1_1637 64 108
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 265
  (Polychromatic418967fa.accept_10_3_8_5_1_606 63 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 108 265 (accept_3_3 62 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 108 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 108 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 108 265 (accept_3_3 59 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 265
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 57 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 108 265 (accept_3_3 56 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 108 265 (Polychromatic418967fa.accept_17_4_6_10_1_5164 55 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 108 265 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 265 (accept_3_3 53 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 265 (Polychromatic418967fa.accept_10_2_8_5_1_587 52 108
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 108 265 (accept_3_3 50 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 108 265 (Polychromatic418967fa.accept_13_10_4_5_1_2331 49 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 108 265 (Polychromatic418967fa.accept_13_9_4_5_1_1651 48 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 265 (accept_3_3 47 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 108 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 265
  (Polychromatic418967fa.accept_8_5_4_1_1_111 45 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 108 265 (accept_3_3 44 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 108 265 (Polychromatic418967fa.accept_10_3_8_5_1_606 43 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 108 265 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 265 (accept_3_3 41 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 265 (Polychromatic418967fa.accept_13_1_4_5_1_113 40 108
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 265
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 108 265 (accept_3_3 38 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 108 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 108 265 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 265 (accept_3_3 35 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 265 (Polychromatic418967fa.accept_16_2_12_9_1_2568 34 108
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 265
  (Polychromatic418967fa.accept_10_3_8_5_1_606 33 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 265 (accept_3_3 32 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 108 265 (Polychromatic418967fa.accept_14_3_10_13_1_339 31 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 108 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 265 (accept_3_3 29 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 265 (Polychromatic418967fa.accept_13_2_4_5_1_3152 28 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 265
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 108 265 (accept_3_3 26 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 108 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 108 265 (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 265 (accept_3_3 23 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 265 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 108
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 265
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 265 (accept_3_3 20 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 108 265 (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 108 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 265 (accept_3_3 17 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 265
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 108 265 (accept_3_3 14 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 108 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 108 265 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 265 (accept_3_3 11 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 265 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 108
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 108 265 (accept_3_3 8 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  108 265 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 108 265 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 265 (accept_3_3 5 108 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 108 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 265
  (Polychromatic418967fa.accept_10_3_8_5_1_606 3 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 108 265 (accept_3_3 2 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  108 265 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 108 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 108
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 265 (allA_of_3_1 107 107 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 265
  (allA_succ_of_accept 105 106 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 106 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 265 (accept_3_3 104 106 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 102 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 106 265 (accept_3_3 101 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 106 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 100 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 265 (accept_3_3 98 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 265 (Polychromatic418967fa.accept_15_7_1_10_1_305 97 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 96 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 265 (accept_3_3 95 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 265 (Polychromatic418967fa.accept_10_4_6_5_1_74 94 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 265 (accept_3_3 92 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 265
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 90 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 106 265 (accept_3_3 89 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 106 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 88 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 265 (accept_3_3 86 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 265 (Polychromatic418967fa.accept_13_7_2_5_1_2344 85 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 265 (accept_3_3 83 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 265 (accept_3_3 80 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 265 (accept_3_3 77 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 76 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 265 (accept_3_3 74 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 265 (accept_3_3 71 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 265 (Polychromatic418967fa.accept_20_10_6_5_1_7776 70 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 265 (accept_3_3 68 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 265 (accept_3_3 65 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 265 (accept_3_3 62 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 265 (accept_3_3 59 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 265 (accept_3_3 56 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 53 106 265 53 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 52 106 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 106 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 106 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 265 (accept_3_3 50 106 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 265 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  49 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 265 (accept_3_3 47 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 265 (accept_3_3 44 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 265 (accept_3_3 41 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 265 (accept_3_3 38 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 265
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 265 (accept_3_3 35 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 265 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 265 (accept_3_3 32 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 265 (accept_3_3 29 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 265 (accept_3_3 26 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 265 (Polychromatic418967fa.accept_13_12_2_5_1_1634 25 106 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 265 (accept_3_3 23 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 265 (Polychromatic418967fa.accept_13_9_2_5_1_2310 22 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 265 (accept_3_3 20 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 265
  (Polychromatic418967fa.accept_27_18_25_22_1_16199 18 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 106 265 (accept_3_3 17 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 106 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 106 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 265 (accept_3_3 14 106 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 265
  (Polychromatic418967fa.accept_15_13_1_10_1_816 13 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 106 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 106 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 106 265 (accept_3_3 11 106 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 106 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 9
  106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 265 (accept_3_3 8 106
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50
  7 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 265 (accept_3_3 5 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 265 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 106 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 265 (accept_3_3 2 106 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 106 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 265 (allA_succ_of_accept 104 105 265 (accept_3_3 104 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 265 (Polychromatic418967fa.accept_13_12_1_5_1_1650 103 105 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 265 (Polychromatic418967fa.accept_9_3_6_4_1_210
  102 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 265 (accept_3_3
  101 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 105 265 5 20 21 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 105 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 99 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 105 265 (accept_3_3 98 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 105 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 97 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 105 265 (Polychromatic418967fa.accept_17_11_3_10_1_2838 96 105 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 105 265 5 19 21 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 105 265
  (Polychromatic418967fa.accept_6_4_3_1_1_57 94 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 265 (accept_3_3 92 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 105 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 105 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 105 265 5 18 21 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 105 265 (accept_3_3 89 105 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 105 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 105 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 87 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 105 265 (accept_3_3 86 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  105 265 5 17 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 105 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 265 (accept_3_3 83 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 105 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 105 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 105 265 (Polychromatic418967fa.accept_13_3_1_5_1_499
  81 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 105 265 5 16 21 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 105 265
  (Polychromatic418967fa.accept_9_7_6_4_1_483 79 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 105 265 (Polychromatic418967fa.accept_14_8_7_13_1_4113 78 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 265 (accept_3_3 77 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 105 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 105 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 105 265 5 15 21 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 105 265 (accept_3_3 74 105 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 105 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 265
  (Polychromatic418967fa.accept_22_6_17_1_1_1004 72 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 105 265 (accept_3_3 71 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  105 265 5 14 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 105 265 (Polychromatic418967fa.accept_13_4_1_5_1_1628 69 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 265 (accept_3_3 68 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 105 265 (Polychromatic418967fa.accept_24_19_9_1_1_9501 67 105 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 105 265 5 13 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 105 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 105 265 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 265 (accept_3_3 62
  105 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 265
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 105 265 5 12 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 105 265 (accept_3_3 59 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 105 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 265 (accept_3_3 56 105 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 105 265 5 11 21 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 105 265
  (Polychromatic418967fa.accept_24_6_9_1_1_11220 54 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 265 (accept_3_3 53 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 265 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 105 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 105 265 5 10 21 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 105 265
  (Polychromatic418967fa.accept_11_5_6_1_1_988 49 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 105 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 265 (accept_3_3 47 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 105 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 105 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 265 5 9 21 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 265 (accept_3_3 44 105 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 105 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 265
  (Polychromatic418967fa.accept_13_3_1_5_1_499 42 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 265 (accept_3_3 41 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  105 265 5 8 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 105 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 265 (accept_3_3 38 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 265 (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 105
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 265 5 7 21 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 265
  (Polychromatic418967fa.accept_6_4_3_1_1_57 34 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 105 265 (Polychromatic418967fa.accept_19_14_10_18_1_5244 33 105 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 265 (accept_3_3 32 105 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 265 (Polychromatic418967fa.accept_25_6_5_15_1_16198 31 105 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 265 5 6 21 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 265 (accept_3_3 29
  105 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 265
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 105 265 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 265 (accept_3_3 26 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 105 265 5 5 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 105 265 (Polychromatic418967fa.accept_17_7_3_10_1_2881 24 105 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 265 (accept_3_3 23 105 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 105 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 105 265 5 4 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 105 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 265 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 105
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 265 (accept_3_3 17 105
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 265
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 105 265 5 3 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 265 (accept_3_3 14 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 105 265 (Polychromatic418967fa.accept_17_13_3_10_1_5157 13 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 105 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 105 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 265 (accept_3_3 11 105 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 265 5 2 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 105 265 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 105 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 265 (accept_3_3 8 105 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 7
  105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 265
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 6 105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 105 265 5 1 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 105 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 105 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 265 (accept_3_3 2 105 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 1
  105 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 265 (allA_of_3_1 104 104 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 265
  (allA_succ_of_accept 102 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 103 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 265 (accept_3_3 101 103 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 265 (Polychromatic418967fa.accept_21_16_19_13_1_7140 100 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 265
  (Polychromatic418967fa.accept_7_1_5_6_1_59 99 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 265 (accept_3_3 98 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 265 (Polychromatic418967fa.accept_10_7_3_5_1_301 97 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 265 (Polychromatic418967fa.accept_11_8_4_1_1_1000 96 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 265 (accept_3_3 95 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 103 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 265
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 93 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 265 (accept_3_3 92 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 265 (Polychromatic418967fa.accept_15_1_13_10_1_1507 91 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 265 (accept_3_3 89 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 88 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 265
  (Polychromatic418967fa.accept_10_7_3_5_1_301 87 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 265 (accept_3_3 86 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 265 (Polychromatic418967fa.accept_13_6_12_5_1_2304 84 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 265 (accept_3_3 83 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 103 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 81 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 265 (accept_3_3 80 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 265 (Polychromatic418967fa.accept_13_1_12_5_1_1601 79 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 265 (accept_3_3 77 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 265 (Polychromatic418967fa.accept_14_6_5_13_1_367 76 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 265
  (Polychromatic418967fa.accept_17_7_1_10_1_2836 75 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 265 (accept_3_3 74 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 265 (Polychromatic418967fa.accept_13_8_12_5_1_1604 73 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 265 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 265 (accept_3_3 71 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 103 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 265
  (Polychromatic418967fa.accept_13_4_12_5_1_476 69 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 265 (accept_3_3 68 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 265 (accept_3_3 65 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 265
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 265 (accept_3_3 62 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 265 (Polychromatic418967fa.accept_15_1_13_10_1_1507 61 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 265 (accept_3_3 59 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 265
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 265 (accept_3_3 56 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 265 (Polychromatic418967fa.accept_20_15_3_5_1_10654 55 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 265 (accept_3_3 53 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 265 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 265
  (Polychromatic418967fa.accept_16_3_7_9_1_3474 51 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 265 (accept_3_3 50 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 265 (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 265 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 265 (accept_3_3 47 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 103 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 265
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 265 (accept_3_3 44 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 265 (accept_3_3 41 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 265 (Polychromatic418967fa.accept_13_1_12_5_1_1601 40 103 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 265 (accept_3_3 38 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 265 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 265 (accept_3_3 35 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 265
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 33 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 265 (accept_3_3 32 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 265 (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 265 (accept_3_3 29 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 265 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 265
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 265 (accept_3_3 26 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 265 (Polychromatic418967fa.accept_16_8_7_9_1_7052 24 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 265 (accept_3_3 23 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 103 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 265
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 265 (accept_3_3 20 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 265 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 265 (accept_3_3 17 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 265 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 103 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 265
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 265 (accept_3_3 14 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 265 (Polychromatic418967fa.accept_16_13_7_9_1_2606 13 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 265 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 265 (accept_3_3 11 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 265
  (Polychromatic418967fa.accept_17_9_1_10_1_2859 9 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 265 (accept_3_3 8 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 265 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 265 (accept_3_3 5 103 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 103 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 265
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 3 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 265 (accept_3_3 2 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 103 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 265 (allA_succ_of_accept 101 102 265 (accept_3_3 101 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 102 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 100 102 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 102 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 265 (accept_3_3 98 102 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 265 (Polychromatic418967fa.accept_9_7_3_4_1_218
  97 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 96 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 265 (accept_3_3 95 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 102 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 94 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 265 (accept_3_3 92 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 265
  (Polychromatic418967fa.accept_11_2_3_1_1_244 90 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 102 265 (accept_3_3 89 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 102 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 265 (accept_3_3 86 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 265 (Polychromatic418967fa.accept_13_7_11_5_1_2302 85 102 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 265
  (Polychromatic418967fa.accept_13_6_11_5_1_133 84 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 102 265 (accept_3_3 83 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 102 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 102 265 (Polychromatic418967fa.accept_13_3_11_5_1_2348 81 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 265 (accept_3_3 80 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 102 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 102 265 (accept_3_3 77 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 102 265 (Polychromatic418967fa.accept_22_10_14_1_1_13148 76 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 265 (accept_3_3 74 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 102 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 265
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 102 265 (accept_3_3 71 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 102 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 102 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 265 (accept_3_3 68 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 265
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 102 265 (accept_3_3 65 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 102 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 265 (accept_3_3 62 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 265 (accept_3_3 59 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 102 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 265 (Polychromatic418967fa.accept_10_7_2_5_1_298 57 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 265 (accept_3_3 56 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 102 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 102 265 (accept_3_3 53 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 102 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 265 (accept_3_3 50 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 265 (Polychromatic418967fa.accept_19_11_7_18_1_5284 49 102 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 265
  (Polychromatic418967fa.accept_10_8_2_5_1_596 48 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 102 265 (accept_3_3 47 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 102 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 102 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 265 (accept_3_3 44 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 265 (accept_3_3 41 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 265 (accept_3_3 38 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 265
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 102 265 (accept_3_3 35 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 102 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 102 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 265 (accept_3_3 32 102 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 265
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 102 265 (accept_3_3 29 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 102 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 265 (accept_3_3 26 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 265
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 265 (accept_3_3 23 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 265 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 265 (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 265 (accept_3_3 20 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 265
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 265 (accept_3_3 17 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 265 (accept_3_3 14 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 265 (accept_3_3 11 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 265 (accept_3_3 8 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 265 (accept_3_3 5 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 265 (Polychromatic418967fa.accept_20_4_2_5_1_4607 4 102 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 265 (accept_3_3 2 102 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 102 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 265 (allA_of_3_1 101 101 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 265 (allA_succ_of_accept 99
  100 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 100 265 (accept_3_3 98 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 100 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 100 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 100 265 5 19 20 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 100 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 94 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 100 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 100 265 (accept_3_3 92 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 100 265 (Polychromatic418967fa.accept_16_11_4_9_1_851 91 100 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 100 265 5 18 20 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 100 265 (accept_3_3 89 100 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 100 265 (Polychromatic418967fa.accept_7_4_2_6_1_337
  88 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 100 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 100 265 (accept_3_3 86 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  100 265 5 17 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 100 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 100 265 (accept_3_3 83 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 100 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 82 100 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 100 265 5 16 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 100 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 100 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 100 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 78
  100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 100 265 (accept_3_3 77
  100 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 100 265
  (Polychromatic418967fa.accept_16_12_4_9_1_4633 76 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 100 265 5 15 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 100 265 (accept_3_3 74 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 100 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 100 265 (Polychromatic418967fa.accept_16_8_4_9_1_4666 72 100
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 100 265 (accept_3_3 71 100
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 100 265 5 14 20 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 100 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 100 265 (accept_3_3 68 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 100 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 100 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 100 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 100 265 5 13 20 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 100 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 64 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 100 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 100 265 (accept_3_3 62 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 100 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 100 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 100 265 5 12 20 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 100 265 (accept_3_3 59 100 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 100
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 100 265 (accept_3_3 56 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  100 265 5 11 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 100 265 (Polychromatic418967fa.accept_13_2_9_5_1_959 54 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 100 265 (accept_3_3 53 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 100 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 100 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 100 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 51
  100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 265 5 10 20 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 265
  (Polychromatic418967fa.accept_21_7_16_13_1_2733 49 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 100 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 100 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 265 (accept_3_3 47 100 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 100 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 100 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 100 265 5 9 20 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 100 265 (accept_3_3 44 100 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 43
  100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 100 265 (accept_3_3 41 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  100 265 5 8 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 100 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 100 265 (accept_3_3 38 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 100 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 100 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 100 265 5 7 20 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 100 265
  (Polychromatic418967fa.accept_9_7_1_4_1_217 34 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 100 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 265 (accept_3_3 32 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 100 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 100 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 265 5 6 20 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 265 (accept_3_3 29 100 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 265 (Polychromatic418967fa.accept_13_2_9_5_1_959 28 100
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 265 (accept_3_3 26 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  100 265 5 5 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 100 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 100 265 (accept_3_3 23 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 100 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 265 5 4 20 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 265
  (Polychromatic418967fa.accept_17_2_15_10_1_5171 19 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 100 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 265 (accept_3_3 17 100 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 100 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 100 265 5 3 20 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 100 265 (accept_3_3 14 100 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 265 (Polychromatic418967fa.accept_8_5_4_1_1_111
  13 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 100 265 (accept_3_3 11 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  100 265 5 2 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 100 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 100 265 (accept_3_3 8 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 100 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 100 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 100 265 5 1 20 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 100 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 100 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 100 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 265 (accept_3_3 2 100 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 100 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 100 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  265 (allA_succ_of_accept 98 99 265 (accept_3_3 98 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 265 (Polychromatic418967fa.accept_19_2_4_18_1_9556 97 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 265 (accept_3_3 95 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 93 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 265 (accept_3_3 92 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 265 (Polychromatic418967fa.accept_10_1_9_5_1_83 91 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 265 (accept_3_3 89 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 265
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 87 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 265 (accept_3_3 86 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 265 (Polychromatic418967fa.accept_22_19_11_1_1_13116 85 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 265 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 265 (accept_3_3 83 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 265
  (Polychromatic418967fa.accept_10_1_9_5_1_83 81 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 265 (accept_3_3 80 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 79 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 265 (accept_3_3 77 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 265 (accept_3_3 74 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 265 (Polychromatic418967fa.accept_17_5_14_10_1_2831 73 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 265 (accept_3_3 71 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 265
  (Polychromatic418967fa.accept_12_9_3_1_1_303 69 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 265 (accept_3_3 68 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 265 (Polychromatic418967fa.accept_24_19_3_1_1_5907 67 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 265 (accept_3_3 65 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 265
  (Polychromatic418967fa.accept_14_7_1_13_1_357 63 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 265 (accept_3_3 62 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 265 (Polychromatic418967fa.accept_16_12_3_9_1_5886 60 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 265 (accept_3_3 59 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 265
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 265 (accept_3_3 56 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 265 (Polychromatic418967fa.accept_13_3_8_5_1_974 55 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 265 (accept_3_3 53 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 265 (accept_3_3 50 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 265 (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 265 (Polychromatic418967fa.accept_15_3_9_10_1_2325 48 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 265 (accept_3_3 47 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 265
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 265 (accept_3_3 44 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 265 (Polychromatic418967fa.accept_19_5_4_18_1_5242 43 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 265 (accept_3_3 41 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 265
  (Polychromatic418967fa.accept_16_7_3_9_1_2557 39 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 265 (accept_3_3 38 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 265 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 265 (accept_3_3 35 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 265 (accept_3_3 32 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 265 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 265 (accept_3_3 29 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 265
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 265 (accept_3_3 26 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 265 (Polychromatic418967fa.accept_13_12_8_5_1_976 25 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 265 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 265 (accept_3_3 23 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 265
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 265 (accept_3_3 20 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 265 (accept_3_3 17 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 265
  (Polychromatic418967fa.accept_19_15_4_18_1_5227 15 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 265 (accept_3_3 14 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 265 (Polychromatic418967fa.accept_17_13_14_10_1_1847 13 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 265 (accept_3_3 11 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 265 (accept_3_3 8 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  265 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 265 (accept_3_3 5 99 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 265
  (Polychromatic418967fa.accept_13_3_8_5_1_974 3 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 265 (accept_3_3 2 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  265 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 99 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 98 265 (allA_of_3_1 98 98 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 265
  (allA_succ_of_accept 96 97 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 97 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 265 (accept_3_3 95 97 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 265 (Polychromatic418967fa.accept_13_3_6_5_1_2336 94 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 93
  97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 265 (accept_3_3 92 97
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 265 (Polychromatic418967fa.accept_9_1_7_4_1_52
  91 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 265
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 90 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 265 (accept_3_3 89 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 265 (Polychromatic418967fa.accept_10_8_7_5_1_602 88 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 87 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 265 (accept_3_3 86 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 265 (Polychromatic418967fa.accept_16_5_1_9_1_4621 85 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 265 (accept_3_3 83 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 265 (Polychromatic418967fa.accept_13_3_6_5_1_2336 81 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 265 (accept_3_3 80 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 265 (Polychromatic418967fa.accept_13_1_6_5_1_1610 79 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 265 (accept_3_3 77 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 265 (Polychromatic418967fa.accept_11_10_9_1_1_2186 76 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 265 (accept_3_3 74 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 265
  (Polychromatic418967fa.accept_10_2_7_5_1_605 72 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 265 (accept_3_3 71 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 265 (Polychromatic418967fa.accept_17_2_12_10_1_9034 70 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 265 (accept_3_3 68 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 265 (Polychromatic418967fa.accept_19_10_2_18_1_6674 67 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 265 (accept_3_3 65 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 265 (accept_3_3 62 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 265 (Polychromatic418967fa.accept_15_1_7_10_1_287 61 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 265 (accept_3_3 59 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 265 (Polychromatic418967fa.accept_10_8_7_5_1_602 58 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 265 (accept_3_3 56 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 265
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 265 (accept_3_3 53 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 265 (Polychromatic418967fa.accept_10_2_7_5_1_605 52 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 265 (accept_3_3 50 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 265 (Polychromatic418967fa.accept_13_10_6_5_1_2297 49 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 265 (accept_3_3 47 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 265 (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 265 (accept_3_3 44 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 97 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 265 (accept_3_3 41 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 265 (Polychromatic418967fa.accept_13_1_6_5_1_1610 40 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 265 (accept_3_3 38 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 265
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 265 (accept_3_3 35 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 265 (Polychromatic418967fa.accept_15_4_7_10_1_807 34 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 265 (accept_3_3 32 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 265 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 265 (accept_3_3 29 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 265 (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 265 (accept_3_3 26 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 265 (Polychromatic418967fa.accept_13_12_6_5_1_2335 25 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 265 (accept_3_3 23 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 265 (Polychromatic418967fa.accept_10_2_7_5_1_605 22 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 265 (accept_3_3 20 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 265
  (Polychromatic418967fa.accept_10_8_7_5_1_602 18 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 265 (accept_3_3 17 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 265 (Polychromatic418967fa.accept_13_3_6_5_1_2336 16 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 265 (accept_3_3 14 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 265 (accept_3_3 11 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 265 (Polychromatic418967fa.accept_19_9_2_18_1_10859 9 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 265 (accept_3_3 8 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 265 (Polychromatic418967fa.accept_23_7_5_12_1_16197 7 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 265 (accept_3_3 5 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  265 (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 97 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 97 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 265 (accept_3_3 2 97 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 97 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 265
  (allA_succ_of_accept 95 96 265 (accept_3_3 95 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  96 265 (Polychromatic418967fa.accept_10_4_6_5_1_74 94 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 96 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 96 265 (accept_3_3 92 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 265
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 90 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 96 265 (accept_3_3 89 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  96 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 88 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 96 265 (Polychromatic418967fa.accept_15_12_6_10_1_1516 87 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 265 (accept_3_3 86 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 96 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 265 (accept_3_3 83 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  96 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 265 (accept_3_3 80 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 265
  (Polychromatic418967fa.accept_7_1_5_6_1_59 78 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 96 265 (accept_3_3 77 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  96 265 (Polychromatic418967fa.accept_14_6_12_13_1_3180 76 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 96 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 265 (accept_3_3 74 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 265
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 72 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 265 (accept_3_3 71 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  96 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 265 (Polychromatic418967fa.accept_10_9_6_5_1_1002 69 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 265 (accept_3_3 68 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 265 (accept_3_3 65 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 265 (Polychromatic418967fa.accept_15_3_6_10_1_1539 63 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 265 (accept_3_3 62 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 96 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 265 (accept_3_3 59 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 265 (Polychromatic418967fa.accept_20_18_16_5_1_9137 58 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 265 (accept_3_3 56 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 265
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 265 (accept_3_3 53 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 265 (Polychromatic418967fa.accept_10_1_6_5_1_304 51 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 265 (accept_3_3 50 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 265 (Polychromatic418967fa.accept_10_9_6_5_1_1002 49 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 265 (accept_3_3 47 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 265 (Polychromatic418967fa.accept_18_9_6_13_1_4499 45 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 265 (accept_3_3 44 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 96 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 265
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 42 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 265 (accept_3_3 41 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 265 (Polychromatic418967fa.accept_19_2_1_18_1_2660 40 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 265 (accept_3_3 38 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 265
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 265 (accept_3_3 35 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 265 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 265 (accept_3_3 32 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 265 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 96 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 265 (accept_3_3 29 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 265 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 265 (accept_3_3 26 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 96 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 265
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 265 (accept_3_3 23 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 265 (accept_3_3 20 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 265 (accept_3_3 17 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 265 (accept_3_3 14 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 265 (Polychromatic418967fa.accept_19_13_1_18_1_5279 13 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 265 (accept_3_3 11 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 265 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 265 (accept_3_3 8 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 265
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 6 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 265 (accept_3_3 5 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  265 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 96 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 96 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 265 (accept_3_3 2 96 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 265
  (allA_of_3_1 95 95 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 265 (allA_succ_of_accept 93 94 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 94 265 (accept_3_3 92 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  94 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 94 265 (Polychromatic418967fa.accept_20_10_14_5_1_3331 90 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 265 (accept_3_3 89 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 88 94 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 94 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 94 265 (accept_3_3 86 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  94 265 (Polychromatic418967fa.accept_16_5_14_9_1_2572 85 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 94 265 (Polychromatic418967fa.accept_11_7_6_1_1_2182 84 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 265 (accept_3_3 83 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 265 (Polychromatic418967fa.accept_11_5_6_1_1_988 82 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 265 (accept_3_3 80 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 265 (Polychromatic418967fa.accept_24_6_22_1_1_16196 78 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 265 (accept_3_3 77 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 265 (Polychromatic418967fa.accept_10_6_4_5_1_615 76 94 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 265 (accept_3_3 74 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 265 (Polychromatic418967fa.accept_11_7_6_1_1_2182 73 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 265 (accept_3_3 71 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 265 (Polychromatic418967fa.accept_20_10_14_5_1_3331 70 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 265 (accept_3_3 68 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 265 (Polychromatic418967fa.accept_10_6_4_5_1_615 66 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 265 (accept_3_3 65 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 265 (accept_3_3 62 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 265 (Polychromatic418967fa.accept_10_1_4_5_1_1031 61 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 265 (accept_3_3 59 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 265 (accept_3_3 56 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 265 (Polychromatic418967fa.accept_13_2_3_5_1_2294 54 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 265 (accept_3_3 53 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 265 (accept_3_3 50 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 265 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 265 (Polychromatic418967fa.accept_13_9_3_5_1_1605 48 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 265 (accept_3_3 47 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 265 (accept_3_3 44 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 265 (Polychromatic418967fa.accept_28_14_10_13_1_16195 42 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 265 (accept_3_3 41 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 265 (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 94 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 265 (accept_3_3 38 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 265 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 265 (accept_3_3 35 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 265 (Polychromatic418967fa.accept_13_8_3_5_1_1636 34 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 265 (accept_3_3 32 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 265 (accept_3_3 29 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 265 (accept_3_3 26 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 265 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 265 (accept_3_3 23 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 265 (Polychromatic418967fa.accept_13_9_3_5_1_1605 22 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 265 (accept_3_3 20 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 265 (accept_3_3 17 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 265 (accept_3_3 14 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 265 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 265 (Polychromatic418967fa.accept_27_12_13_22_1_16194 12 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 265 (accept_3_3 11 94 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 265 (Polychromatic418967fa.accept_18_10_4_13_1_3296 10 94
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 265 (accept_3_3 8 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 265 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 94 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 265 (accept_3_3 5 94 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 94 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 265 (accept_3_3 2 94 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 265 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1
  94 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 265
  (allA_succ_of_accept 92 93 265 (accept_3_3 92 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 265 (Polychromatic418967fa.accept_13_12_2_5_1_1634 90 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 265 (accept_3_3 89 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 93 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 87 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 265 (accept_3_3 86 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 85 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 265 (accept_3_3 83 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 81 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 265 (accept_3_3 80 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 265 (accept_3_3 77 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 265 (accept_3_3 74 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 265 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 265 (accept_3_3 71 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 265 (accept_3_3 68 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 265 (accept_3_3 65 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 265 (accept_3_3 62 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 265 (accept_3_3 59 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 265 (accept_3_3 56 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 265 (Polychromatic418967fa.accept_15_9_3_10_1_2312 54 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 265 (accept_3_3 53 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 265 (accept_3_3 50 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 265 (Polychromatic418967fa.accept_13_10_2_5_1_1633 49 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 265 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 265 (accept_3_3 47 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 265 (accept_3_3 44 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 265 (accept_3_3 41 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 265 (accept_3_3 38 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 265 (accept_3_3 35 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 265 (accept_3_3 32 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 265 (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 265 (accept_3_3 29 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 265
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 265 (accept_3_3 26 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 265 (accept_3_3 23 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 265
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 21 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 265 (accept_3_3 20 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 265 (accept_3_3 17 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 265 (accept_3_3 14 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 265 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 265 (accept_3_3 11 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 93 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 265
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 265 (accept_3_3 8 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  265 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 93 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 93 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 265 (accept_3_3 5 93 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 93
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 265 (accept_3_3 2 93 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 93
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 265
  (allA_of_3_1 92 92 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 265 (allA_succ_of_accept 90 91 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 265 (accept_3_3 89 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 87 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 265 (accept_3_3 86 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 265 (Polychromatic418967fa.accept_14_1_7_13_1_333 85 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 91 265 (accept_3_3 83 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 265 (Polychromatic418967fa.accept_15_6_1_10_1_1549 81 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 265 (accept_3_3 80 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 91 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 91 265 (accept_3_3 77 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 265 (Polychromatic418967fa.accept_10_6_1_5_1_1024 76 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 265 (accept_3_3 74 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 73 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 265
  (Polychromatic418967fa.accept_17_4_6_10_1_5164 72 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 265 (accept_3_3 71 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 265 (accept_3_3 68 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 265 (Polychromatic418967fa.accept_15_7_1_10_1_305 67 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 265 (accept_3_3 65 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 265 (Polychromatic418967fa.accept_10_4_1_5_1_1018 64 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 265 (Polychromatic418967fa.accept_17_12_6_10_1_7807 63 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 265 (accept_3_3 62 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 91 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 265 (accept_3_3 59 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 265 (accept_3_3 56 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 265 (Polychromatic418967fa.accept_17_4_6_10_1_5164 55 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 265 (accept_3_3 53 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 265 (accept_3_3 50 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 265 (accept_3_3 47 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 265 (Polychromatic418967fa.accept_19_7_15_18_1_8132 45 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 265 (accept_3_3 44 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 91 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 265 (accept_3_3 41 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 265 (Polychromatic418967fa.accept_19_2_15_18_1_1556 40 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 265 (accept_3_3 38 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 265 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 265
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 265 (accept_3_3 35 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 265 (accept_3_3 32 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 265 (Polychromatic418967fa.accept_19_12_15_18_1_9544 31 91 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 265 (accept_3_3 29 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 265 (Polychromatic418967fa.accept_21_6_7_13_1_7199 27 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 265 (accept_3_3 26 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 91 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 265 (accept_3_3 23 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 265 (accept_3_3 20 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 265 (accept_3_3 17 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 265 (accept_3_3 14 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 265 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 265 (accept_3_3 11 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 265 (accept_3_3 8 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 265 (accept_3_3 5 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  265 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 91 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 265 (accept_3_3 2 91 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 265 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 91 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 265
  (allA_succ_of_accept 89 90 265 (accept_3_3 89 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  90 265 (Polychromatic418967fa.accept_20_8_10_5_1_6083 88 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 265 (accept_3_3 86 90 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 85 90 265 5 17 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 90 265 (Polychromatic418967fa.accept_13_6_12_5_1_2304 84 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 90 265 (accept_3_3 83 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 265 (Polychromatic418967fa.accept_13_4_12_5_1_476
  82 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 90 265
  (Polychromatic418967fa.accept_16_1_10_9_1_4645 81 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 265 5 16 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 90 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 265 (Polychromatic418967fa.accept_20_18_10_5_1_3306 78 90
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 265 (accept_3_3 77 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 90 265 (Polychromatic418967fa.accept_11_10_2_1_1_1036
  76 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 265 5 15 18 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 265 (accept_3_3 74
  90 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 265
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 73 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 90 265 (Polychromatic418967fa.accept_13_7_12_5_1_1603 72 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 265 (accept_3_3 71 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 90 265 5 14 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 90 265 (Polychromatic418967fa.accept_11_3_2_1_1_994 69 90 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 265 (accept_3_3 68 90 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 265
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 66 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 90 265 5 13 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 90 265 (Polychromatic418967fa.accept_17_13_5_10_1_2839 64 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 90 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 265 (accept_3_3 62 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 265 (Polychromatic418967fa.accept_14_5_6_13_1_3145
  61 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 265 5 12 18 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 265 (accept_3_3 59
  90 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 265
  (Polychromatic418967fa.accept_11_3_2_1_1_994 58 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 90 265 (Polychromatic418967fa.accept_20_17_10_5_1_7765 57 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 265 (accept_3_3 56 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 90 265 5 11 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 90 265 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 90 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 265 (accept_3_3 53 90 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 265 (Polychromatic418967fa.accept_20_12_10_5_1_4661 52 90
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 265 5 10 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 265 (Polychromatic418967fa.accept_14_7_6_13_1_4111 49 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 265 (Polychromatic418967fa.accept_17_14_5_10_1_9052 48 90
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 265 (accept_3_3 47 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 265 (Polychromatic418967fa.accept_13_7_12_5_1_1603
  46 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 90 265 5 9 18 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 90 265 (accept_3_3 44
  90 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 90 265 (Polychromatic418967fa.accept_19_4_14_18_1_5234 42 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 265 (accept_3_3 41 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 90 265 5 8 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 90 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 265 (accept_3_3 38 90 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 265 (Polychromatic418967fa.accept_20_17_10_5_1_7765 37 90 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 265
  (Polychromatic418967fa.accept_11_3_2_1_1_994 36 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 90 265 5 7 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 90 265 (Polychromatic418967fa.accept_13_8_12_5_1_1604 34 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 265 (Polychromatic418967fa.accept_13_7_12_5_1_1603 33 90
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 265 (accept_3_3 32 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 265 5 6 18 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 265 (accept_3_3 29
  90 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 265
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 28 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 90 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 265 (accept_3_3 26 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 90 265 5 5 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 90 265 (Polychromatic418967fa.accept_20_4_10_5_1_3305 24 90 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 265 (accept_3_3 23 90 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 265 (Polychromatic418967fa.accept_19_3_14_18_1_6685 22 90 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 265
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 265 5 4 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 265 (Polychromatic418967fa.accept_20_18_10_5_1_3306 18 90
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 265 (accept_3_3 17 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 265
  (Polychromatic418967fa.accept_19_16_14_18_1_6684 16 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 90 265 5 3 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 90 265 (accept_3_3 14 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 265 (Polychromatic418967fa.accept_17_13_5_10_1_2839 13 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 265 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 90
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 265 (accept_3_3 11 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 265 5 2 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 265 (Polychromatic418967fa.accept_20_9_10_5_1_6085 9
  90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 265 (accept_3_3 8 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 265
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 90 265 5 1 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 90 265 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 90 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 265 (accept_3_3 2 90 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 265 (Polychromatic418967fa.accept_13_1_12_5_1_1601
  1 90 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 265
  (allA_of_3_1 89 89 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 265 (allA_succ_of_accept 87 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 88 265 (accept_3_3 86 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  88 265 (Polychromatic418967fa.accept_19_9_12_18_1_8099 85 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 88 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 265 (accept_3_3 83 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 88 265 (accept_3_3 80 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  88 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 88 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 265 (accept_3_3 77 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 265 (Polychromatic418967fa.accept_15_1_13_10_1_1507 76 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 265 (accept_3_3 74 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 265 (accept_3_3 71 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 265 (accept_3_3 68 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 265 (Polychromatic418967fa.accept_10_7_8_5_1_1008 67 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 88 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 265 (accept_3_3 65 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 88 265 (accept_3_3 62 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  88 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 88 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 265 (accept_3_3 59 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 265 (accept_3_3 56 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 265 (accept_3_3 53 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 265 (accept_3_3 50 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 265 (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 265 (accept_3_3 47 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 265 (accept_3_3 44 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 265 (Polychromatic418967fa.accept_10_3_8_5_1_606 43 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 265 (accept_3_3 41 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 265 (accept_3_3 38 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 265 (Polychromatic418967fa.accept_16_4_8_9_1_4639 36 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 265 (accept_3_3 35 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 265 (accept_3_3 32 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 265 (accept_3_3 29 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 265 (accept_3_3 26 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 265 (Polychromatic418967fa.accept_19_6_12_18_1_8141 25 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 265 (accept_3_3 23 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 265 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 265 (accept_3_3 20 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 265 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 265 (accept_3_3 17 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 88 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 265 (accept_3_3 14 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 265 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 265 (accept_3_3 11 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 265 (accept_3_3 8 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  265 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 88 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 265 (accept_3_3 5 88 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 88 265 (Polychromatic418967fa.accept_13_4_10_5_1_1644 4 88 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 88 265 (accept_3_3 2 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88
  265 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 88 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87
  265 (allA_succ_of_accept 86 87 265 (accept_3_3 86 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 87 265 (Polychromatic418967fa.accept_26_7_9_5_1_16193 85 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 265 (accept_3_3 83 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 265
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 265 (accept_3_3 80 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 265 (accept_3_3 77 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 265 (accept_3_3 74 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 265 (accept_3_3 71 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 265
  (Polychromatic418967fa.accept_12_9_3_1_1_303 69 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 265 (accept_3_3 68 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 265 (accept_3_3 65 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 265
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 265 (accept_3_3 62 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 265 (accept_3_3 59 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 265 (accept_3_3 56 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 265 (accept_3_3 53 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 265 (accept_3_3 50 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 265 (Polychromatic418967fa.accept_17_15_2_10_1_9021 49 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 265 (accept_3_3 47 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 265
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 265 (accept_3_3 44 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 265 (accept_3_3 41 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 265
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 265 (accept_3_3 38 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 265 (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 265 (accept_3_3 35 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 265
  (Polychromatic418967fa.accept_10_3_7_5_1_288 33 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 265 (accept_3_3 32 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 265 (Polychromatic418967fa.accept_11_9_10_1_1_581 31 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 265 (accept_3_3 29 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 265
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 265 (accept_3_3 26 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 265 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 265 (accept_3_3 23 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 265 (accept_3_3 20 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 265 (accept_3_3 17 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 265
  (Polychromatic418967fa.accept_13_2_9_5_1_959 15 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 265 (accept_3_3 14 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 265 (accept_3_3 11 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 265 (accept_3_3 8 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  265 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 265 (accept_3_3 5 87 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  87 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 265 (accept_3_3 2 87 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 87
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 265
  (allA_of_3_1 86 86 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 265 (allA_succ_of_accept 84 85 265
  (Polychromatic418967fa.accept_8_4_5_1_1_299 84 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 265 (accept_3_3 83 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 265 (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 85 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 85 265 5 16 17 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 85 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 265 (Polychromatic418967fa.accept_16_14_5_9_1_5901 78 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 265 (accept_3_3 77 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 76 85 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 85 265 5 15 17 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 85 265 (accept_3_3 74 85 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 265 (Polychromatic418967fa.accept_19_16_9_18_1_8127 73 85
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 265 (accept_3_3 71 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 85
  265 5 14 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  85 265 (Polychromatic418967fa.accept_19_12_9_18_1_16189 69 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 85 265 (accept_3_3 68 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 85 265 (Polychromatic418967fa.accept_13_2_7_5_1_3189 67 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 265 (Polychromatic418967fa.accept_25_16_10_15_1_16192 66 85
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 85 265 5 13 17 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 85 265
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 64 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 85 265 (Polychromatic418967fa.accept_13_11_7_5_1_2314 63 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 265 (accept_3_3 62 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 85 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 85 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 85 265 5 12 17 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 85 265 (accept_3_3 59 85 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 85 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 265
  (Polychromatic418967fa.accept_24_9_13_1_1_12883 57 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 265 (accept_3_3 56 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 85
  265 5 11 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  85 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 85 265 (accept_3_3 53 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 85 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 85 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 85 265 5 10 17 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 85 265
  (Polychromatic418967fa.accept_14_7_1_13_1_357 49 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 85 265 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 265 (accept_3_3 47 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 85 265 (Polychromatic418967fa.accept_16_14_5_9_1_5901 46 85 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 265 5 9 17 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 265 (accept_3_3 44 85 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 265 (Polychromatic418967fa.accept_16_11_5_9_1_1617 43 85
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 265
  (Polychromatic418967fa.accept_22_20_19_1_1_16191 42 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 85 265 (accept_3_3 41 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 85 265 5 8 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 85 265 (Polychromatic418967fa.accept_25_14_10_15_1_16190 39 85 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 265 (accept_3_3 38 85 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 85 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 265
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 85 265 5 7 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 85 265 (Polychromatic418967fa.accept_19_15_9_18_1_9552 34 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 85 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 265 (accept_3_3 32 85 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 265
  (Polychromatic418967fa.accept_19_12_9_18_1_16189 31 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 85 265 5 6 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 85 265 (accept_3_3 29 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 85 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 265 (Polychromatic418967fa.accept_16_11_5_9_1_1617 27 85
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 265 (accept_3_3 26 85 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85 265 5 5 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 85 265 (Polychromatic418967fa.accept_13_11_7_5_1_2314
  24 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 265 (accept_3_3 23
  85 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 265
  (Polychromatic418967fa.accept_19_3_9_18_1_10979 22 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 85 265 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 85 265 5 4 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 85 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 85 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 265
  (Polychromatic418967fa.accept_22_18_19_1_1_16188 18 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 85 265 (accept_3_3 17 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 85 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 265 5 3 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 265 (accept_3_3 14 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 85 265 (Polychromatic418967fa.accept_16_13_5_9_1_4682 13 85 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 265 (accept_3_3 11 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85
  265 5 2 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  85 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 85 265 (accept_3_3 8 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 85 265 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 265 (Polychromatic418967fa.accept_19_6_9_18_1_8140 6 85 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 85 265 5 1 17 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 85 265
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 85 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 265 (Polychromatic418967fa.accept_19_3_9_18_1_10979 3 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 265 (accept_3_3 2 85 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 265 (Polychromatic418967fa.accept_16_1_5_9_1_1649 1 85 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 265
  (allA_succ_of_accept 83 84 265 (accept_3_3 83 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 265 (Polychromatic418967fa.accept_10_1_4_5_1_1031 81 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 265 (accept_3_3 80 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 84 265 (accept_3_3 77 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  84 265 (Polychromatic418967fa.accept_10_6_4_5_1_615 76 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 84 265 (Polychromatic418967fa.accept_13_10_6_5_1_2297 75 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 265 (accept_3_3 74 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 84 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 265
  (Polychromatic418967fa.accept_11_6_7_1_1_564 72 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 265 (accept_3_3 71 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 265 (accept_3_3 68 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 265 (Polychromatic418967fa.accept_19_10_8_18_1_2669 67 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 265
  (Polychromatic418967fa.accept_10_6_4_5_1_615 66 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 84 265 (accept_3_3 65 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  84 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 265 (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 265 (accept_3_3 62 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 84 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 265 (accept_3_3 59 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 265 (Polychromatic418967fa.accept_17_7_16_10_1_1849 58 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 265 (Polychromatic418967fa.accept_15_12_9_10_1_2326 57 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 265 (accept_3_3 56 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 84 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 265
  (Polychromatic418967fa.accept_19_16_8_18_1_8139 54 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 265 (accept_3_3 53 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  84 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 265 (accept_3_3 50 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 265 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 265
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 48 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 265 (accept_3_3 47 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 265 (accept_3_3 44 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 265 (accept_3_3 41 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 265 (Polychromatic418967fa.accept_13_1_6_5_1_1610 40 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 265 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 265 (accept_3_3 38 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 265
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 265 (accept_3_3 35 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 265 (accept_3_3 32 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 265 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 265
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 30 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 265 (accept_3_3 29 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 265 (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 265 (accept_3_3 26 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 265 (accept_3_3 23 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 265 (Polychromatic418967fa.accept_20_2_4_5_1_13401 22 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 265 (accept_3_3 20 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 265
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 265 (accept_3_3 17 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 265 (accept_3_3 14 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 265
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 265 (accept_3_3 11 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 265 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 265 (accept_3_3 8 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 265 (accept_3_3 5 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  265 (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 84 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 84 265 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 265 (accept_3_3 2 84 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 265 (allA_of_3_1
  83 83 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 265 (allA_succ_of_accept 81 82 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 265 (accept_3_3 80 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 265 (accept_3_3 77 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 76 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 265 (accept_3_3 74 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 73 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 265 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 265 (accept_3_3 71 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 265 (accept_3_3 68 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 265 (accept_3_3 65 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 265 (accept_3_3 62 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 265 (accept_3_3 59 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 265 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 265 (accept_3_3 56 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 265 (Polychromatic418967fa.accept_13_2_4_5_1_3152 54 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 265 (accept_3_3 53 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 265 (accept_3_3 50 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 265 (Polychromatic418967fa.accept_13_10_4_5_1_2331 49 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 265 (accept_3_3 47 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 265 (accept_3_3 44 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 265 (accept_3_3 41 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 265 (accept_3_3 38 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 265 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 265 (accept_3_3 35 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 265 (accept_3_3 32 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 265 (accept_3_3 29 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 265 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 265 (accept_3_3 26 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 265 (accept_3_3 23 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 265 (accept_3_3 20 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 265 (accept_3_3 17 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 265 (accept_3_3 14 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 265 (accept_3_3 11 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 265 (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 82 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 265 (accept_3_3 8 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 82 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 265 (accept_3_3 5 82 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 82 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 265 (accept_3_3 2 82 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 82
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 265
  (allA_succ_of_accept 80 81 265 (accept_3_3 80 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 265 (Polychromatic418967fa.accept_15_3_6_10_1_1539 78 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 265 (accept_3_3 77 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 265 (accept_3_3 74 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 265 (accept_3_3 71 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 265
  (Polychromatic418967fa.accept_10_9_1_5_1_594 69 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 265 (accept_3_3 68 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 265 (Polychromatic418967fa.accept_13_2_3_5_1_2294 67 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 265 (accept_3_3 65 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 265
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 265 (accept_3_3 62 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 265 (Polychromatic418967fa.accept_13_8_3_5_1_1636 60 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 265 (accept_3_3 59 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 265
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 57 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 265 (accept_3_3 56 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 265 (Polychromatic418967fa.accept_19_17_5_18_1_6646 55 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 265 (accept_3_3 53 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 265
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 265 (accept_3_3 50 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 265 (Polychromatic418967fa.accept_13_9_3_5_1_1605 48 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 265 (accept_3_3 47 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 265
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 265 (accept_3_3 44 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 265 (Polychromatic418967fa.accept_17_9_13_10_1_1825 43 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 265 (Polychromatic418967fa.accept_15_12_6_10_1_1516 42 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 265 (accept_3_3 41 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 265
  (Polychromatic418967fa.accept_10_9_1_5_1_594 39 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 265 (accept_3_3 38 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 265 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 265 (accept_3_3 35 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 265 (accept_3_3 32 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 265 (accept_3_3 29 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 265 (accept_3_3 26 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 265 (Polychromatic418967fa.accept_19_6_5_18_1_5228 25 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 265 (accept_3_3 23 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 265
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 265 (accept_3_3 20 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 265 (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 265 (accept_3_3 17 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 265 (accept_3_3 14 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 265 (Polychromatic418967fa.accept_16_13_1_9_1_2597 13 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 265 (accept_3_3 11 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 265
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 265 (accept_3_3 8 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  265 (Polychromatic418967fa.accept_21_7_18_13_1_5585 7 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 265 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 265 (accept_3_3 5 81 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 265
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 265 (accept_3_3 2 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  265 (Polychromatic418967fa.accept_13_1_3_5_1_140 1 81 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 265
  (allA_of_3_1 80 80 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 265 (allA_succ_of_accept 78 79 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 265 (accept_3_3 77 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 265 (Polychromatic418967fa.accept_10_6_9_5_1_1046 76 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 265 (accept_3_3 74 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 265
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 72 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 265 (accept_3_3 71 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 265 (accept_3_3 68 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 265 (accept_3_3 65 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 265 (Polychromatic418967fa.accept_19_6_3_18_1_5262 63 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 265 (accept_3_3 62 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 265 (Polychromatic418967fa.accept_10_1_9_5_1_83 61 79 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 265 (accept_3_3 59 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 265 (accept_3_3 56 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 265 (accept_3_3 53 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 265 (accept_3_3 50 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 265 (Polychromatic418967fa.accept_19_11_3_18_1_10828 49 79 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 265 (accept_3_3 47 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 265 (accept_3_3 44 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 265 (accept_3_3 41 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 265 (Polychromatic418967fa.accept_16_8_15_9_1_4676 40 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 265 (accept_3_3 38 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 265 (accept_3_3 35 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 265 (accept_3_3 32 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 265 (accept_3_3 29 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 265 (Polychromatic418967fa.accept_21_6_16_13_1_4100 27 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 265 (accept_3_3 26 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 79 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 265 (accept_3_3 23 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 265 (accept_3_3 20 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 265 (accept_3_3 17 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 265 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 265 (accept_3_3 14 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 265 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 265 (accept_3_3 11 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 265 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 265 (accept_3_3 8 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 265 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 79 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 265 (accept_3_3 5 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  265 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 79 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 79 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 265 (accept_3_3 2 79 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 79 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 265
  (allA_succ_of_accept 77 78 265 (accept_3_3 77 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 265 (Polychromatic418967fa.accept_20_16_18_5_1_4638 76 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 265 (accept_3_3 74 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 265 (accept_3_3 71 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 265 (Polychromatic418967fa.accept_15_9_3_10_1_2312 69 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 265 (accept_3_3 68 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 265 (accept_3_3 65 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 265 (accept_3_3 62 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 265
  (Polychromatic418967fa.accept_19_3_2_18_1_9566 60 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 265 (accept_3_3 59 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 265 (accept_3_3 56 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 265 (accept_3_3 53 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 265 (accept_3_3 50 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 265 (Polychromatic418967fa.accept_14_7_8_13_1_3161 49 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 265 (accept_3_3 47 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 265 (Polychromatic418967fa.accept_18_9_6_13_1_4499 45 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 265 (accept_3_3 44 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 265
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 265 (accept_3_3 41 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 265 (accept_3_3 38 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 265
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 265 (accept_3_3 35 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 265 (accept_3_3 32 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 265 (accept_3_3 29 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 265 (accept_3_3 26 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 265
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 265 (accept_3_3 23 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 265 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 265 (accept_3_3 20 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 265
  (Polychromatic418967fa.accept_21_18_15_13_1_4130 18 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 78 265 (accept_3_3 17 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 78 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 265 (accept_3_3 14 78 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 265 (Polychromatic418967fa.accept_10_3_8_5_1_606
  13 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 265 (accept_3_3 11 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 265 (accept_3_3 8 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 265
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 6 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 265 (accept_3_3 5 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  265 (Polychromatic418967fa.accept_16_4_14_9_1_4657 4 78 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 78 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 265 (accept_3_3 2 78 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 265 (allA_of_3_1 77 77
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 265 (allA_succ_of_accept 75 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 265 (accept_3_3 74 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 73 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 265 (Polychromatic418967fa.accept_13_7_11_5_1_2302 72 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 265 (accept_3_3 71 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 76
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 265 (accept_3_3 68 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 265 (Polychromatic418967fa.accept_15_7_1_10_1_305 67 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 265 (Polychromatic418967fa.accept_15_6_1_10_1_1549 66 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 265 (accept_3_3 65 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 265 (Polychromatic418967fa.accept_10_4_6_5_1_74 64 76 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 265 (accept_3_3 62 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 265 (Polychromatic418967fa.accept_24_12_4_1_1_16187 60 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 265 (accept_3_3 59 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 76
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 265 (accept_3_3 56 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 265 (Polychromatic418967fa.accept_13_3_11_5_1_2348 55 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 265 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 76 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 265 (accept_3_3 53 76 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 265 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 265 (accept_3_3 50 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 265 (Polychromatic418967fa.accept_10_9_6_5_1_1002 49 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 265 (Polychromatic418967fa.accept_23_2_7_12_1_14588 48 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 265 (accept_3_3 47 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 265 (Polychromatic418967fa.accept_11_2_10_1_1_1017 46 76
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 265 (accept_3_3 44 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 43 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 265 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 76 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 265 (accept_3_3 41 76 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 265 (Polychromatic418967fa.accept_14_12_6_13_1_3173 40 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 265 (accept_3_3 38 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 265 (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 265 (accept_3_3 35 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 265 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 76 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 265 (accept_3_3 32 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 265 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 265 (Polychromatic418967fa.accept_20_10_16_5_1_3311 30 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 265 (accept_3_3 29 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 76
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 265 (accept_3_3 26 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 265 (Polychromatic418967fa.accept_18_7_4_13_1_3315 25 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 265 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 76 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 265 (accept_3_3 23 76 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 265 (accept_3_3 20 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 265 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 265 (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 265 (accept_3_3 17 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 265 (Polychromatic418967fa.accept_13_3_11_5_1_2348 16 76
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 265 (accept_3_3 14 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 265 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 265 (accept_3_3 11 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 76
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 265 (accept_3_3 8 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  265 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 76 265 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 76 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 265 (accept_3_3 5 76 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 76 265 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 76 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 76 265 (accept_3_3 2 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76
  265 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 76 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 265
  (allA_succ_of_accept 74 75 265 (accept_3_3 74 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  75 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 75 265 (Polychromatic418967fa.accept_20_12_15_5_1_9169 72 75 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 265 (accept_3_3 71 75 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 75 265 5 14 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 75 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 69
  75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 265 (accept_3_3 68 75
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 75 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 75 265 5 13 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 64
  75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 265
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 63 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 75 265 (accept_3_3 62 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  75 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 75 265 5 12 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 75 265 (accept_3_3 59 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 75 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 75 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 265 (accept_3_3 56 75 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 265 5 11 15 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 75 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 265 (accept_3_3 53 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 75 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 75 265 5 10 15 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 265
  (Polychromatic418967fa.accept_20_9_15_5_1_4670 49 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 75 265 (Polychromatic418967fa.accept_14_6_5_13_1_367 48 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 265 (accept_3_3 47 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 75 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 265 5 9 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 265 (accept_3_3 44 75 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 75 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 265 (accept_3_3 41 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75
  265 5 8 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  75 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 75 265 (accept_3_3 38 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 75 265 5 7 15 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 75 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 265 (accept_3_3 32 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 75 265 (Polychromatic418967fa.accept_17_14_7_10_1_7808 31 75 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 265 5 6 15 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 265 (accept_3_3 29 75 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 265
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 27 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 265 (accept_3_3 26 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75
  265 5 5 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  75 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 265 (accept_3_3 23 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 265 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 75
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 265 5 4 15 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 265
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 75 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 265 (accept_3_3 17 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 75 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 265 5 3 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 265 (accept_3_3 14 75 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 265 (Polychromatic418967fa.accept_20_13_15_5_1_4628 13 75 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 265
  (Polychromatic418967fa.accept_18_12_3_13_1_4494 12 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 265 (accept_3_3 11 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75
  265 5 2 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  75 265 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 265 (accept_3_3 8 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 265 5 1 15 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 265
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 265 (Polychromatic418967fa.accept_17_3_7_10_1_3948 3 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 265 (accept_3_3 2 75 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 75 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 265 (allA_of_3_1 74 74
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 265 (allA_succ_of_accept 72 73 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 265 (accept_3_3 71 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 265 (accept_3_3 68 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 265 (accept_3_3 65 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 265 (Polychromatic418967fa.accept_13_12_8_5_1_976 64 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 265 (Polychromatic418967fa.accept_15_3_13_10_1_2332 63 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 265 (accept_3_3 62 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 73 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 265
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 265 (accept_3_3 59 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 265 (accept_3_3 56 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 265 (Polychromatic418967fa.accept_13_3_8_5_1_974 55 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 265
  (Polychromatic418967fa.accept_23_8_4_12_1_11384 54 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 265 (accept_3_3 53 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 265 (accept_3_3 50 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 265 (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 265 (accept_3_3 47 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 265 (Polychromatic418967fa.accept_21_3_10_13_1_16174 45 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 265 (accept_3_3 44 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 73 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 265 (accept_3_3 41 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 265 (Polychromatic418967fa.accept_13_1_8_5_1_2315 40 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 265 (accept_3_3 38 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 265
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 265 (accept_3_3 35 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 265 (accept_3_3 32 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 265 (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 265 (accept_3_3 29 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 265 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 265 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 265 (accept_3_3 26 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 265 (accept_3_3 23 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 265 (Polychromatic418967fa.accept_10_2_3_5_1_996 22 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 265 (accept_3_3 20 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 265 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 265
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 265 (accept_3_3 17 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 265 (accept_3_3 14 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 265 (Polychromatic418967fa.accept_17_13_5_10_1_2839 13 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 265 (accept_3_3 11 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 265 (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 265 (accept_3_3 8 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 265 (accept_3_3 5 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  265 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 73 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 73 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 265 (accept_3_3 2 73 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 265 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1 73 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 265 (allA_succ_of_accept 71
  72 265 (accept_3_3 71 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 265
  (Polychromatic418967fa.accept_20_10_12_5_1_4687 70 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 265 (Polychromatic418967fa.accept_15_9_12_10_1_809 69 72 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 265 (accept_3_3 68 72 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 66
  72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 265 (accept_3_3 65 72
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 265 (Polychromatic418967fa.accept_7_1_2_6_1_55
  64 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 72 265
  (Polychromatic418967fa.accept_10_3_2_5_1_295 63 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 72 265 (accept_3_3 62 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  72 265 (Polychromatic418967fa.accept_19_4_15_18_1_10821 61 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 72 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 265 (accept_3_3 59 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 72 265 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 72 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 72 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 72 265 (accept_3_3 56 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  72 265 (Polychromatic418967fa.accept_16_7_8_9_1_9427 55 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 72 265 (Polychromatic418967fa.accept_13_2_7_5_1_3189 54 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 265 (accept_3_3 53 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 72 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 72 265
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 72 265 (accept_3_3 50 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  72 265 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 72 265 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 265 (accept_3_3 47 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 72 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 72 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 72 265 (accept_3_3 44 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  72 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 72 265 (Polychromatic418967fa.accept_19_4_15_18_1_10821 42 72 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 265 (accept_3_3 41 72 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 265 (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 72 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 72 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 72 265 (accept_3_3 38 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  72 265 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 72 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 265 (accept_3_3 35 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 265 (Polychromatic418967fa.accept_23_11_3_12_1_16186 34 72 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 72 265
  (Polychromatic418967fa.accept_10_3_2_5_1_295 33 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 72 265 (accept_3_3 32 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  72 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 72 265 (Polychromatic418967fa.accept_20_10_12_5_1_4687 30 72 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 265 (accept_3_3 29 72 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 265 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 72 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 72 265
  (Polychromatic418967fa.accept_10_7_2_5_1_298 27 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 72 265 (accept_3_3 26 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  72 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 72 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 265 (accept_3_3 23 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 72 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 72 265
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 72 265 (accept_3_3 20 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  72 265 (Polychromatic418967fa.accept_23_19_3_12_1_16185 19 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 72 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 265 (accept_3_3 17 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 265 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 72 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 72 265 (accept_3_3 14 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  72 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 72 265 (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 72 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 265 (accept_3_3 11 72 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 72 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 265
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 72 265 (accept_3_3 8 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72
  265 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 72 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 72 265 (Polychromatic418967fa.accept_15_6_12_10_1_1543 6 72 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 265 (accept_3_3 5 72 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 72 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 72 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 265 (accept_3_3 2 72 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 265 (allA_of_3_1 71 71 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 265 (allA_succ_of_accept 69 70 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 265 (accept_3_3 68 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 70 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 70 265 5 13 14 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 70 265
  (Polychromatic418967fa.accept_9_1_7_4_1_52 64 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 70 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 265 (accept_3_3 62 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 70 265 (Polychromatic418967fa.accept_16_13_6_9_1_2561 61 70 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 265 5 12 14 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 265 (accept_3_3 59 70 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 265
  (Polychromatic418967fa.accept_19_1_13_18_1_6700 58 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 70 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 70 265 (accept_3_3 56 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 70 265 5 11 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 70 265 (Polychromatic418967fa.accept_19_16_13_18_1_8152 54 70 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 265 (accept_3_3 53 70 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 265 (Polychromatic418967fa.accept_11_8_4_1_1_1000 52 70 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 70 265 5 10 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 70 265 (Polychromatic418967fa.accept_17_15_2_10_1_9021 49 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 70 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 70 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 265 (accept_3_3 47 70 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 46
  70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 70 265 5 9 14 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 70 265 (accept_3_3 44
  70 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 70 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 265 (accept_3_3 41 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 70 265 5 8 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 70 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 265 (accept_3_3 38 70 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 70 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 265
  (Polychromatic418967fa.accept_19_17_13_18_1_9542 36 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 70 265 5 7 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 70 265 (Polychromatic418967fa.accept_16_2_6_9_1_3473 34 70 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 265 (accept_3_3 32 70
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 265 (Polychromatic418967fa.accept_4_3_2_1_1_50
  31 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 265 5 6 14 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 265 (accept_3_3 29
  70 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 265
  (Polychromatic418967fa.accept_9_1_7_4_1_52 28 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 70 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 265 (accept_3_3 26 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 70 265 5 5 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 70 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 70 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 265 (accept_3_3 23 70 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 265 (Polychromatic418967fa.accept_20_2_10_5_1_6082 22 70 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 265 5 4 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 265 (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 70 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 265 (accept_3_3 17 70 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 265 (Polychromatic418967fa.accept_12_4_10_1_1_706
  16 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 70 265 5 3 14 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 70 265 (accept_3_3 14
  70 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 265
  (Polychromatic418967fa.accept_16_13_6_9_1_2561 13 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 70 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 265 (accept_3_3 11 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 70 265 5 2 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 70 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 265 (accept_3_3 8 70 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 70 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 70 265 5 1 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 70 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 70 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 265 (accept_3_3 2 70 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 265 (allA_succ_of_accept 68 69
  265 (accept_3_3 68 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 265
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 67 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 69 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 265 (accept_3_3 65 69 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 265 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 265 (accept_3_3 62
  69 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 265
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 69 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 69 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 265 (accept_3_3 59 69 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 69 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 57
  69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 265 (accept_3_3 56 69
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 265 (Polychromatic418967fa.accept_9_1_6_4_1_49
  55 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 265
  (Polychromatic418967fa.accept_10_4_9_5_1_84 54 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 69 265 (accept_3_3 53 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  69 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 265 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 265 (accept_3_3 50 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 265 (Polychromatic418967fa.accept_13_10_4_5_1_2331 49 69 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 69 265 (accept_3_3 47 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  69 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 265 (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 265 (accept_3_3 44 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 69 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 265
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 42 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 265 (accept_3_3 41 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  69 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 265 (accept_3_3 38 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 69 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 265
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 265 (accept_3_3 35 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  69 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 265 (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 69 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 265 (accept_3_3 32 69 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 265 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 69 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 265 (accept_3_3 29 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 265 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 265 (accept_3_3 26 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 69 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 265
  (Polychromatic418967fa.accept_10_4_9_5_1_84 24 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 265 (accept_3_3 23 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  69 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 265 (accept_3_3 20 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 69 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 265
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 265 (accept_3_3 17 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 265 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 265 (accept_3_3 14 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 265 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 69 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 265
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 265 (accept_3_3 11 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 265 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 265 (accept_3_3 8 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 69 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 265
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 265 (accept_3_3 5 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 69 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 265 (accept_3_3 2 69 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 69 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 265 (allA_of_3_1 68 68 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 265 (allA_succ_of_accept 66 67 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 265 (accept_3_3 65 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 265 (Polychromatic418967fa.accept_13_12_2_5_1_1634 64 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 265 (accept_3_3 62 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 265
  (Polychromatic418967fa.accept_16_12_3_9_1_5886 60 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 265 (accept_3_3 59 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 265 (Polychromatic418967fa.accept_15_12_7_10_1_3297 57 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 265 (accept_3_3 56 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 265 (Polychromatic418967fa.accept_13_3_2_5_1_1632 55 67 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 265 (accept_3_3 53 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 265 (accept_3_3 50 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 265 (Polychromatic418967fa.accept_13_10_2_5_1_1633 49 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 265
  (Polychromatic418967fa.accept_10_8_7_5_1_602 48 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 265 (accept_3_3 47 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 265 (accept_3_3 44 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 265 (accept_3_3 41 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 265 (Polychromatic418967fa.accept_16_7_3_9_1_2557 39 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 265 (accept_3_3 38 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 265
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 265 (accept_3_3 35 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 265 (accept_3_3 32 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 265 (accept_3_3 29 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 265 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 265 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 265 (accept_3_3 26 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 265 (Polychromatic418967fa.accept_13_12_2_5_1_1634 25 67
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 265
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 265 (accept_3_3 23 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 265 (Polychromatic418967fa.accept_19_2_10_18_1_6691 21 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 265 (accept_3_3 20 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 265 (accept_3_3 17 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 265 (Polychromatic418967fa.accept_20_15_7_5_1_2115 15 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 265 (accept_3_3 14 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 67 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 265 (accept_3_3 11 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 265 (accept_3_3 8 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 265 (Polychromatic418967fa.accept_13_7_2_5_1_2344 7 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 265 (accept_3_3 5 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  265 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 67 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 265 (accept_3_3 2 67 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 265 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 67 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 265 (allA_succ_of_accept 65 66
  265 (accept_3_3 65 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 265
  (Polychromatic418967fa.accept_9_1_3_4_1_47 64 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 265 (accept_3_3 62 66 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 60
  66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 265 (accept_3_3 59 66
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 265 (Polychromatic418967fa.accept_7_2_3_6_1_4
  58 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 66 265
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 57 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 66 265 (accept_3_3 56 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  66 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 66 265 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 265 (accept_3_3 53 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 66 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 66 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 66 265 (accept_3_3 50 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  66 265 (Polychromatic418967fa.accept_10_9_6_5_1_1002 49 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 66 265 (Polychromatic418967fa.accept_13_9_1_5_1_964 48 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 265 (accept_3_3 47 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 66 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 66 265
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 45 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 66 265 (accept_3_3 44 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  66 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 66 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 265 (accept_3_3 41 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 265 (Polychromatic418967fa.accept_19_2_9_18_1_6651 40 66 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 66 265 (accept_3_3 38 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  66 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 66 265 (Polychromatic418967fa.accept_17_2_15_10_1_5171 36 66 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 265 (accept_3_3 35 66 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 66 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 66 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 66 265 (accept_3_3 32 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  66 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 66 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 265 (accept_3_3 29 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 66 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 66 265 (accept_3_3 26 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  66 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 66 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 265 (accept_3_3 23 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 265 (Polychromatic418967fa.accept_13_9_1_5_1_964 22 66 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 265
  (Polychromatic418967fa.accept_10_1_6_5_1_304 21 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 66 265 (accept_3_3 20 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  66 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 66 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 265 (accept_3_3 17 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 66 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 265 (accept_3_3 14 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  66 265 (Polychromatic418967fa.accept_19_13_9_18_1_10939 13 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 265 (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 66 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 265 (accept_3_3 11 66 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 66 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 265 (accept_3_3 8 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66
  265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 66 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 265 (accept_3_3 5 66 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 66 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 265 (accept_3_3 2 66 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 66
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 265 (allA_of_3_1 65 65 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 265 (allA_succ_of_accept 63 64 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 265 (accept_3_3 62 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 265 (accept_3_3 59 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 64 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 265 (accept_3_3 56 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 265 (Polychromatic418967fa.accept_18_1_10_13_1_500 55 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 265 (accept_3_3 53 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 64 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 265 (accept_3_3 50 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 265 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 265 (accept_3_3 47 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 265 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 64 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 265 (accept_3_3 44 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 265 (accept_3_3 41 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 64 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 265 (accept_3_3 38 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 265 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 265 (accept_3_3 35 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 64 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 265 (accept_3_3 32 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 265 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 265 (accept_3_3 29 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 265 (Polychromatic418967fa.accept_13_2_12_5_1_1602 28 64 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 265 (accept_3_3 26 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 265 (accept_3_3 23 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 64 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 265 (accept_3_3 20 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 265 (Polychromatic418967fa.accept_22_18_20_1_1_11609 18 64 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 265 (accept_3_3 17 64 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 64 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 265 (accept_3_3 14 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 265 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 265 (accept_3_3 11 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 265 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 64 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 265 (accept_3_3 8 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  265 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 64 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 265 (accept_3_3 5 64 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 265 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 64 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 265 (accept_3_3 2 64 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 265 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1
  64 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 265 (allA_succ_of_accept 62 63 265
  (accept_3_3 62 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 265
  (Polychromatic418967fa.accept_20_1_3_5_1_1060 61 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 265 (Polychromatic418967fa.accept_18_6_9_13_1_3320 60 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 265 (accept_3_3 59 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 265 (Polychromatic418967fa.accept_10_7_3_5_1_301
  57 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 265 (accept_3_3 56
  63 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 265
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 55 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 265 (accept_3_3 53 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 63 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 265 (Polychromatic418967fa.accept_15_6_3_10_1_2341
  51 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 265 (accept_3_3 50
  63 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 265
  (Polychromatic418967fa.accept_19_11_6_18_1_2717 49 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 63 265 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 265 (accept_3_3 47 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 63 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 265 (Polychromatic418967fa.accept_12_9_3_1_1_303
  45 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 265 (accept_3_3 44
  63 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 265
  (Polychromatic418967fa.accept_14_1_7_13_1_333 43 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 63 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 265 (accept_3_3 41 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 63 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 265 (Polychromatic418967fa.accept_15_9_3_10_1_2312
  39 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 265 (accept_3_3 38
  63 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 265
  (Polychromatic418967fa.accept_10_7_3_5_1_301 37 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 63 265 (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 265 (accept_3_3 35 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 63 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 265 (Polychromatic418967fa.accept_12_9_3_1_1_303
  33 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 265 (accept_3_3 32
  63 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 265
  (Polychromatic418967fa.accept_19_12_6_18_1_8095 31 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 63 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 265 (accept_3_3 29 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 63 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 265 (Polychromatic418967fa.accept_10_7_3_5_1_301
  27 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 265 (accept_3_3 26
  63 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 265
  (Polychromatic418967fa.accept_17_8_12_10_1_6442 25 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 63 265 (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 265 (accept_3_3 23 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 63 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 265 (Polychromatic418967fa.accept_12_9_3_1_1_303
  21 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 265 (accept_3_3 20
  63 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 265
  (Polychromatic418967fa.accept_13_6_11_5_1_133 19 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 63 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 265 (accept_3_3 17 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 63 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 265 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  15 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 265 (accept_3_3 14
  63 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 265
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 63 265 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 265 (accept_3_3 11 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 63 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 265 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 265 (accept_3_3 8 63 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 265 (Polychromatic418967fa.accept_10_7_3_5_1_301 7
  63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 265 (accept_3_3 5 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 63 265 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 265 (accept_3_3 2 63 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 63 265 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 63 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 265 (allA_of_3_1 62 62 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 265 (allA_succ_of_accept 60 61 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 265 (accept_3_3 59 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 58 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 265 (accept_3_3 56 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 61 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 265
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 265 (accept_3_3 53 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 265 (accept_3_3 50 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 61 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 265 (accept_3_3 47 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 265 (Polychromatic418967fa.accept_24_21_13_1_1_12867 45 61 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 265 (accept_3_3 44 61 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 61 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 265 (accept_3_3 41 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 265 (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 265 (accept_3_3 38 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 61 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 265
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 265 (accept_3_3 35 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 265 (Polychromatic418967fa.accept_10_4_1_5_1_1018 34 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 265 (accept_3_3 32 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 265 (Polychromatic418967fa.accept_24_7_13_1_1_9522 31 61 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 265 (accept_3_3 29 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 265 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 265 (accept_3_3 26 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 61 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 265 (accept_3_3 23 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 265 (accept_3_3 20 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 265 (accept_3_3 17 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 265 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 265 (accept_3_3 14 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 61 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 265
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 265 (accept_3_3 11 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 265 (accept_3_3 8 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 265 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 61 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 265 (accept_3_3 5 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  265 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 61 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 61 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 265 (accept_3_3 2 61 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 265 (allA_succ_of_accept 59 60 265 (accept_3_3 59 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 60 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 265 (accept_3_3 56 60 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 265 5 11 12 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 60 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 265 (accept_3_3 53 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 265 5 10 12 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 265
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 60 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 265 (accept_3_3 47 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 60 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 60 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 265 5 9 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 265 (accept_3_3 44 60 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 60 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 265
  (Polychromatic418967fa.accept_13_3_8_5_1_974 42 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 265 (accept_3_3 41 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60
  265 5 8 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  60 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 265 (accept_3_3 38 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 60 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 265 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 60
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 60 265 5 7 12 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 265
  (Polychromatic418967fa.accept_9_7_6_4_1_483 34 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 60 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 265 (accept_3_3 32 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 60 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 60 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 265 5 6 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 265 (accept_3_3 29 60 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 60 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 265
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 60 265 (accept_3_3 26 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60
  265 5 5 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  60 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 60 265 (accept_3_3 23 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 265 (Polychromatic418967fa.accept_28_22_4_13_1_16184 22 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 265 5 4 12 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 60 265 (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 265 (accept_3_3 17 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 60 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 60 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 265 5 3 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 265 (accept_3_3 14 60 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 60 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 265 (accept_3_3 11 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60
  265 5 2 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  60 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 265 (accept_3_3 8 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 265 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 60 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 60 265 5 1 12 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 265
  (Polychromatic418967fa.accept_16_4_12_9_1_2567 4 60 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 265 (accept_3_3 2 60 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 60 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 265 (allA_of_3_1 59 59 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 265
  (allA_succ_of_accept 57 58 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 58 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 265 (accept_3_3 56 58 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 265 (Polychromatic418967fa.accept_17_3_7_10_1_3948
  54 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 265 (accept_3_3 53
  58 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 52 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 265 (accept_3_3 50 58 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 265 (Polychromatic418967fa.accept_13_10_6_5_1_2297 49 58 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 265
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 48 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 58 265 (accept_3_3 47 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 265 (accept_3_3 44 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 265
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 265 (accept_3_3 41 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 265 (accept_3_3 38 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 265 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 58 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 265 (accept_3_3 35 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 265 (Polychromatic418967fa.accept_15_4_13_10_1_1508 34 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 265 (accept_3_3 32 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 265
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 30 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 265 (accept_3_3 29 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 265 (accept_3_3 26 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 58 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 265 (accept_3_3 23 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 265 (accept_3_3 20 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 265 (accept_3_3 17 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 265 (accept_3_3 14 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 265 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 58 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 265
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 265 (accept_3_3 11 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 265 (accept_3_3 8 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 265
  (Polychromatic418967fa.accept_19_6_1_18_1_13556 6 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 265 (accept_3_3 5 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  265 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 58 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 265 (accept_3_3 2 58 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 58 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 265))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 57 265 (allA_succ_of_accept 56 57 265 (accept_3_3 56 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 57 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 57 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 57 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 265 (accept_3_3 53 57 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 52
  57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 265 (accept_3_3 50 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  57 265 (Polychromatic418967fa.accept_14_7_1_13_1_357 49 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 265 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 265 (accept_3_3 47 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 57 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 265
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 45 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 57 265 (accept_3_3 44 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  57 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 57 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 265 (accept_3_3 41 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 57 265 (accept_3_3 38 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  57 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 57 265 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 265 (accept_3_3 35 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 265 (accept_3_3 32 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  57 265 (Polychromatic418967fa.accept_20_11_17_5_1_13413 31 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 265 (accept_3_3 29 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 265
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 265 (accept_3_3 26 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  57 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 265 (accept_3_3 23 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 265
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 265 (accept_3_3 20 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 265 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 265 (accept_3_3 17 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 265 (accept_3_3 14 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 265 (accept_3_3 11 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 265 (accept_3_3 8 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  265 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 57 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 57 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 265 (accept_3_3 5 57 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 57 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 3
  57 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 265 (accept_3_3 2 57 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 57
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  265))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 265 (allA_of_3_1 56 56 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 55 265 (allA_succ_of_accept 54 55 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 265 (accept_3_3 53 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 55 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 265 5 10 11 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 265
  (Polychromatic418967fa.accept_17_15_4_10_1_3968 49 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 265 (accept_3_3 47 55 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 265 5 9 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 265 (accept_3_3 44 55 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 55 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 265 (accept_3_3 41 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  265 5 8 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 265 (accept_3_3 38 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 265 (Polychromatic418967fa.accept_13_11_3_5_1_982 37 55 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 265 (Polychromatic418967fa.accept_20_16_15_5_1_7740 36 55
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 265 5 7 11 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 55 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 265 (accept_3_3 32 55 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 265 (Polychromatic418967fa.accept_19_12_17_18_1_14776 31 55 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 265 5 6 11 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 265 (accept_3_3 29 55 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 265 (Polychromatic418967fa.accept_13_2_3_5_1_2294 28 55 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 265
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 265 (accept_3_3 26 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  265 5 5 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 265 (accept_3_3 23 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 55 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 265 5 4 11 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 265
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 19 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 265 (accept_3_3 17 55 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 55 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 265 5 3 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 265 (accept_3_3 14 55 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 265 (Polychromatic418967fa.accept_16_13_7_9_1_2606 13 55 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 265 (accept_3_3 11 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  265 5 2 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 265 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 55 265 (accept_3_3 8 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 55 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 265 5 1 11 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 265
  (Polychromatic418967fa.accept_19_4_17_18_1_9536 4 55 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 55 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 265 (accept_3_3 2 55 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 265 (Polychromatic418967fa.accept_13_1_3_5_1_140 1 55 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 265)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 265 (allA_succ_of_accept 53 54 265 (accept_3_3 53 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 265 (Polychromatic418967fa.accept_19_14_16_18_1_9534 52 54 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 54 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 265 (accept_3_3 50 54 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 265 (Polychromatic418967fa.accept_10_9_4_5_1_616
  49 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 265
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 48 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 265 (accept_3_3 47 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 265 (Polychromatic418967fa.accept_16_13_6_9_1_2561 45 54 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 265 (accept_3_3 44 54 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 265
  (Polychromatic418967fa.accept_11_9_10_1_1_581 42 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 265 (accept_3_3 41 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 265 (Polychromatic418967fa.accept_19_2_16_18_1_10922 40 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 265 (accept_3_3 38 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 265 (Polychromatic418967fa.accept_25_12_4_15_1_16183 37 54 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 265
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 265 (accept_3_3 35 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 265 (Polychromatic418967fa.accept_14_6_12_13_1_3180 34 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 265 (Polychromatic418967fa.accept_13_7_2_5_1_2344 33 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 265 (accept_3_3 32 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 265
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 265 (accept_3_3 29 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 265 (Polychromatic418967fa.accept_17_11_3_10_1_2838 28 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 265 (accept_3_3 26 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 54 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 265
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 265 (accept_3_3 23 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 265 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 265 (accept_3_3 20 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 265 (accept_3_3 17 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 265 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 265 (accept_3_3 14 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 265 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 54 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 265
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 265 (accept_3_3 11 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 265 (Polychromatic418967fa.accept_13_10_2_5_1_1633 10 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 265 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 265 (accept_3_3 8 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 265
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 265 (accept_3_3 5 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  265 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 54 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 54 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 265 (accept_3_3 2 54 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 54 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 54 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 265))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 265 (allA_of_3_1 53 53 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 265
  (allA_succ_of_accept 51 52 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 265 (accept_3_3 50 52 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 265 (Polychromatic418967fa.accept_15_4_7_10_1_807 49 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 48
  52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 265 (accept_3_3 47 52
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 265
  (Polychromatic418967fa.accept_7_4_3_6_1_340 46 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 265 (accept_3_3 44 52 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 43 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 42
  52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 265 (accept_3_3 41 52
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 265
  (Polychromatic418967fa.accept_16_8_4_9_1_4666 40 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 52 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 265 (accept_3_3 38 52 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 52 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 265
  (Polychromatic418967fa.accept_22_14_8_1_1_14681 36 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 265 (accept_3_3 35 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 265 (accept_3_3 32 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 265 (Polychromatic418967fa.accept_14_3_10_13_1_339 31 52 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 265 (accept_3_3 29 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 265 (accept_3_3 26 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 52 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 265 (accept_3_3 23 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 265 (accept_3_3 20 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 52 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 265
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 265 (accept_3_3 17 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 265 (accept_3_3 14 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 52 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 265 (accept_3_3 11 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 265 (accept_3_3 8 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 265 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 52 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 265 (accept_3_3 5 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  265 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 52 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 265 (accept_3_3 2 52 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 52 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 265))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 265 (allA_succ_of_accept 50 51 265 (accept_3_3 50 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 51 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 51 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 265 (accept_3_3 47 51 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 265 (accept_3_3 44 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 265 (accept_3_3 41 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 265 (accept_3_3 38 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 265 (accept_3_3 35 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 265
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 265 (accept_3_3 32 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 265 (accept_3_3 29 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 265
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 265 (accept_3_3 26 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 265 (accept_3_3 23 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 265 (accept_3_3 20 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 265 (accept_3_3 17 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 265 (accept_3_3 14 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 265 (Polychromatic418967fa.accept_27_13_24_22_1_16182 13 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 265 (accept_3_3 11 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 265
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 265 (accept_3_3 8 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  265 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 51 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 265 (accept_3_3 5 51 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 265 (accept_3_3 2 51 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 51
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  265))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 265 (allA_of_3_1 50 50 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 265 (allA_succ_of_accept 48 49 265 (Polychromatic418967fa.accept_14_6_7_13_1_3158
  48 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 265 (accept_3_3 47
  49 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 265
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 46 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 49 265 (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 49 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 265 (accept_3_3 44 49 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 49 265 (Polychromatic418967fa.accept_13_4_10_5_1_1644 43 49 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 265
  (Polychromatic418967fa.accept_16_10_1_9_1_4622 42 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 265 (accept_3_3 41 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 265 (Polychromatic418967fa.accept_16_8_1_9_1_847 40 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 265 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 49 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 265 (accept_3_3 38 49 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 265 (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 49 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 265
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 265 (accept_3_3 35 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 265 (Polychromatic418967fa.accept_10_4_9_5_1_84 34 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 265 (Polychromatic418967fa.accept_25_8_24_15_1_16181 33 49 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 265 (accept_3_3 32 49 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 265 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 49 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 265
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 30 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 265 (accept_3_3 29 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 265 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 265 (Polychromatic418967fa.accept_19_8_11_18_1_14800 27 49 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 265 (accept_3_3 26 49 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 265 (Polychromatic418967fa.accept_17_8_15_10_1_10367 25 49
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 265
  (Polychromatic418967fa.accept_10_4_9_5_1_84 24 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 265 (accept_3_3 23 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 265 (Polychromatic418967fa.accept_14_8_7_13_1_4113 22 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 265 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 49 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 265 (accept_3_3 20 49 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 265 (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 49 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 265
  (Polychromatic418967fa.accept_16_2_1_9_1_2577 18 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 265 (accept_3_3 17 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 265 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 265 (Polychromatic418967fa.accept_13_2_10_5_1_1643 15 49 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 265 (accept_3_3 14 49 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 265 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 49
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 265
  (Polychromatic418967fa.accept_19_12_11_18_1_10844 12 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 49 265 (accept_3_3 11 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 49 265 (Polychromatic418967fa.accept_16_10_1_9_1_4622 10 49 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 265 (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 49 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 265 (accept_3_3 8 49 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 265 (Polychromatic418967fa.accept_15_7_4_10_1_1513
  7 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 265
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 265 (accept_3_3 5 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  265 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 49 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 265 (Polychromatic418967fa.accept_19_3_11_18_1_2709 3 49 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 265 (accept_3_3 2 49 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 265 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 49 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 265))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 265 (allA_succ_of_accept 47 48 265 (accept_3_3 47 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 48 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 265 (Polychromatic418967fa.accept_19_7_10_18_1_6695 45 48
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 265 (accept_3_3 44 48 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 43
  48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 265 (accept_3_3 41 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  48 265 (Polychromatic418967fa.accept_13_1_9_5_1_1598 40 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 265 (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 48 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 265 (accept_3_3 38 48 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 48 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 265
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 265 (accept_3_3 35 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 265 (accept_3_3 32 48 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 265 (Polychromatic418967fa.accept_25_6_23_15_1_16180 31 48 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 265
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 265 (accept_3_3 29 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 265 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 48 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 265 (accept_3_3 26 48 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 48 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 265 (accept_3_3 23 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 265 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 265 (Polychromatic418967fa.accept_14_7_6_13_1_4111 21 48 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 265 (accept_3_3 20 48 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 265
  (Polychromatic418967fa.accept_17_1_14_10_1_10151 18 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 48 265 (accept_3_3 17 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 48 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 265 (accept_3_3 14 48 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 265 (Polychromatic418967fa.accept_10_3_8_5_1_606
  13 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 265
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 265 (accept_3_3 11 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 265 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 48 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 265 (accept_3_3 8 48 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 265 (accept_3_3 5 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  265 (Polychromatic418967fa.accept_13_4_9_5_1_1641 4 48 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 48 265 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 48 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 265 (accept_3_3 2 48 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 265))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 47 265 (allA_of_3_1 47 47 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 265
  (allA_succ_of_accept 45 46 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 265 (accept_3_3 44 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 46 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 42
  46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 265 (accept_3_3 41 46
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 40 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 46 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 265 (accept_3_3 38 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 46 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 46 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 265 (Polychromatic418967fa.accept_11_3_2_1_1_994
  36 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 265 (accept_3_3 35
  46 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 265
  (Polychromatic418967fa.accept_9_7_1_4_1_217 34 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 46 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 265 (accept_3_3 32 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 46 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 30
  46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 265 (accept_3_3 29 46
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 265
  (Polychromatic418967fa.accept_12_4_10_1_1_706 28 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 265 (accept_3_3 26 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 24
  46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 265 (accept_3_3 23 46
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 265
  (Polychromatic418967fa.accept_15_7_1_10_1_305 22 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 46 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 265 (accept_3_3 20 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 46 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 265
  (Polychromatic418967fa.accept_21_18_4_13_1_5602 18 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 46 265 (accept_3_3 17 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  46 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 46 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 265 (accept_3_3 14 46 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 46 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 46 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 46 265 (accept_3_3 11 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  46 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 46 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 265 (accept_3_3 8 46 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 46 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 46 265 (accept_3_3 5 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46
  265 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 46 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 46 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 265 (accept_3_3 2 46 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 46 265 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 46 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 265)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45
  265 (allA_succ_of_accept 44 45 265 (accept_3_3 44 45 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 45 265 (Polychromatic418967fa.accept_13_4_6_5_1_2333 43 45 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 45 265 (Polychromatic418967fa.accept_13_3_6_5_1_2336 42 45 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 265 (accept_3_3 41 45 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 265 5 8 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 45 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 45 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 265 (accept_3_3 38 45 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 45 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 265
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 45 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 45 265 5 7 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 45 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 265 (Polychromatic418967fa.accept_16_1_13_9_1_2551 33 45
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 265 (accept_3_3 32 45 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 265
  (Polychromatic418967fa.accept_19_12_7_18_1_8110 31 45 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 265 5 6 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 265 (accept_3_3 29 45 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 265 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 45 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 265 (accept_3_3 26 45 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 265 5 5 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 45 265 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 45 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 265 (accept_3_3 23 45 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 45 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 265
  (Polychromatic418967fa.accept_16_5_13_9_1_2594 21 45 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 45 265 5 4 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 265 (Polychromatic418967fa.accept_29_19_16_4_1_16179 19 45 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 265 (accept_3_3 17 45 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  45 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 265 5 3 9 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 265 (accept_3_3 14
  45 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 265
  (Polychromatic418967fa.accept_23_13_22_12_1_11395 13 45 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 45 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 265 (accept_3_3 11 45 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 265 5 2 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 45 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 265 (accept_3_3 8 45 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 265 (Polychromatic418967fa.accept_16_7_13_9_1_1653 7 45 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 265
  (Polychromatic418967fa.accept_16_6_13_9_1_4690 6 45 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 45 265 5 1 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 265 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 45 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 265 (accept_3_3 2 45 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 265 (Polychromatic418967fa.accept_13_1_6_5_1_1610 1
  45 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  265))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 265 (allA_of_3_1 44 44 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 265 (allA_succ_of_accept 42 43 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 265 (accept_3_3 41 43 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 40
  43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 265 (accept_3_3 38 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 265 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 43 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 265 (accept_3_3 35 43 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 265 (accept_3_3 32 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 265 (Polychromatic418967fa.accept_11_9_10_1_1_581 31 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 265 (accept_3_3 29 43 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 265
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 265 (accept_3_3 26 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 265 (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 43 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 265 (accept_3_3 23 43 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 265
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 265 (accept_3_3 20 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 265 (accept_3_3 17 43 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 43 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 265 (accept_3_3 14 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 265 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 43 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 265 (accept_3_3 11 43 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 265 (accept_3_3 8 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  265 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 265 (accept_3_3 5 43 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 265 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 43 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 43
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 265 (accept_3_3 2 43 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  265))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 265 (allA_succ_of_accept 41 42 265 (accept_3_3 41 42 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 265 (Polychromatic418967fa.accept_13_1_3_5_1_140
  40 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 42 265 (accept_3_3 38 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  42 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 42 265 (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 42 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 265 (accept_3_3 35 42 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 42 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 265
  (Polychromatic418967fa.accept_10_3_2_5_1_295 33 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 42 265 (accept_3_3 32 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  42 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 42 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 42 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 265 (accept_3_3 29 42 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 42 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 42 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 42 265 (accept_3_3 26 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  42 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 42 265 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 42 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 265 (accept_3_3 23 42 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 265 (Polychromatic418967fa.accept_13_9_3_5_1_1605 22 42 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 42 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 42 265 (accept_3_3 20 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  42 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 42 265 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 42 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 265 (accept_3_3 17 42 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 42 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 42 265 (accept_3_3 14 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  42 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 42 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 42 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 265 (accept_3_3 11 42 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 42 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 42 265
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 265 (accept_3_3 8 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42
  265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 42 265 (Polychromatic418967fa.accept_13_6_3_5_1_3167 6 42 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 265 (accept_3_3 5 42 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 42 265 (Polychromatic418967fa.accept_20_4_2_5_1_4607 4 42 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 265 (accept_3_3 2 42 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  265)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 265 (allA_of_3_1 41 41 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 265 (allA_succ_of_accept 39 40 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 40 265 (accept_3_3 38 40 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 40 265
  (Polychromatic418967fa.accept_21_16_19_13_1_7140 37 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 40 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 40 265 5 7 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 40 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843
  34 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 265 (accept_3_3 32 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 265 (Polychromatic418967fa.accept_16_15_8_9_1_2563 31 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 40 265 5 6 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 40 265 (accept_3_3 29 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 40 265 (Polychromatic418967fa.accept_11_6_7_1_1_564 28 40 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 265 (accept_3_3 26 40 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 40 265 5 5 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 40 265 (Polychromatic418967fa.accept_19_5_2_18_1_2716
  24 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 265 (accept_3_3 23
  40 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 265
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 40 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 265 5 4 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 265 (Polychromatic418967fa.accept_13_6_1_5_1_3988 19 40 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 265
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 40 265 (accept_3_3 17 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  40 265 (Polychromatic418967fa.accept_13_3_1_5_1_499 16 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 40 265 5 3 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 40 265 (accept_3_3 14 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 40 265 (Polychromatic418967fa.accept_22_13_18_1_1_16178 13 40 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 265 (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 40
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 265 (accept_3_3 11 40 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 265 5 2 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 265 (accept_3_3 8 40 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 265 (Polychromatic418967fa.accept_16_7_8_9_1_9427 7
  40 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 265
  (Polychromatic418967fa.accept_11_6_7_1_1_564 6 40 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 40 265 5 1 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 40 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 40 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 265 (accept_3_3 2 40 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 40
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  265)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 265 (allA_succ_of_accept 38 39 265 (accept_3_3 38 39 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 37
  39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 265
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 265 (accept_3_3 35 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 39 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 265 (accept_3_3 32 39 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 39 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 265 (accept_3_3 29 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 265 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 39 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 265 (accept_3_3 26 39 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 39 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 265
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 265 (accept_3_3 23 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 265 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 39 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 265 (accept_3_3 20 39 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 39 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 265 (accept_3_3 17 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 39 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 265 (accept_3_3 14 39 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 265 (Polychromatic418967fa.accept_16_13_7_9_1_2606 13 39 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 265
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 265 (accept_3_3 11 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 39 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 265 (accept_3_3 8 39 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 39 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 265 (accept_3_3 5 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 265 (accept_3_3 2 39 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 39 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 265))))))))))))))))))))))))))))))))))))))) (allB_succ 38 265
  (allA_of_3_1 38 38 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 265 (allA_succ_of_accept 36 37 265
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 265 (accept_3_3 35 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 37 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 265 (accept_3_3 32 37 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 37 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 265 (accept_3_3 29 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 265 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 37 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 265 (accept_3_3 26 37 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 37 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 265
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 265 (accept_3_3 23 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 37 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 265 (accept_3_3 20 37 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 265 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 37 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 265
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 265 (accept_3_3 17 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 37 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 265 (accept_3_3 14 37 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 37 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 265
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 265 (accept_3_3 11 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 265 (Polychromatic418967fa.accept_17_9_3_10_1_9070 9 37 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 265 (accept_3_3 8 37 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 265 (accept_3_3 5 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  265 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 37 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 37 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 265 (accept_3_3 2 37 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 265))))))))))))))))))))))))))))))))))))) (allB_succ 36 265
  (allA_succ_of_accept 35 36 265 (accept_3_3 35 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 265 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 265 (accept_3_3 32 36 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 265 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 36 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 265
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 265 (accept_3_3 29 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 265 (Polychromatic418967fa.accept_13_2_10_5_1_1643 28 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 265 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 36 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 265 (accept_3_3 26 36 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 265 (Polychromatic418967fa.accept_17_8_2_10_1_2879 25 36
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 265
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 265 (accept_3_3 23 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 265 (Polychromatic418967fa.accept_23_22_13_12_1_6297 22 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 265 (accept_3_3 20 36 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 265
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 265 (accept_3_3 17 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 265 (Polychromatic418967fa.accept_13_2_10_5_1_1643 15 36 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 265 (accept_3_3 14 36 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 36 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 265 (accept_3_3 11 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 265 (Polychromatic418967fa.accept_19_10_17_18_1_9555 10 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 265 (accept_3_3 8 36 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 265 (Polychromatic418967fa.accept_14_7_8_13_1_3161 7 36 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 265
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 6 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 265 (accept_3_3 5 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  265 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 36 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 36 265 (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 36 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 265 (accept_3_3 2 36 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 36 265 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 36 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 265)))))))))))))))))))))))))))))))))))) (allB_succ 35 265
  (allA_of_3_1 35 35 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 265 (allA_succ_of_accept 33 34 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 265 (accept_3_3 32 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 34 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 265 (accept_3_3 29 34 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 34 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 265 (accept_3_3 26 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 265 (Polychromatic418967fa.accept_13_12_8_5_1_976 25 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 34 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 265 (accept_3_3 23 34 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 265 (Polychromatic418967fa.accept_15_7_4_10_1_1513 22 34 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 265 (accept_3_3 20 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 265 (Polychromatic418967fa.accept_25_18_9_15_1_16177 18 34 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 265 (accept_3_3 17 34 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 265 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 34 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 265 (accept_3_3 14 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 265 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 34 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 265 (accept_3_3 11 34 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 34 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 265 (accept_3_3 8 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 34 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 265 (accept_3_3 5 34 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 34 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 265 (accept_3_3 2 34 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 34
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 265))))))))))))))))))))))))))))))))))
  (allB_succ 33 265 (allA_succ_of_accept 32 33 265 (accept_3_3 32 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 265 (Polychromatic418967fa.accept_23_8_10_12_1_16176 31 33 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 33 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 265 (accept_3_3 29 33 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  33 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 265
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 265 (accept_3_3 26 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 265 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 33 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 265 (accept_3_3 23 33 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 33 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 265 (accept_3_3 20 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 265 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 265 (accept_3_3 17 33 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 265
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 265 (accept_3_3 14 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 265 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 265 (accept_3_3 11 33 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 265
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 265 (accept_3_3 8 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  265 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 33 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 265 (Polychromatic418967fa.accept_14_6_5_13_1_367 6 33 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 265 (accept_3_3 5 33 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  33 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 265 (accept_3_3 2 33 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 33
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 265)))))))))))))))))))))))))))))))))
  (allB_succ 32 265 (allA_of_3_1 32 32 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 265
  (allA_succ_of_accept 30 31 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 265 (accept_3_3 29 31 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 31 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 265
  (Polychromatic418967fa.accept_22_5_9_1_1_16175 27 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 265 (accept_3_3 26 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 265 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 31 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 265 (accept_3_3 23 31 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 265
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 265 (accept_3_3 20 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 265 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 265 (accept_3_3 17 31 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 31 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 265
  (Polychromatic418967fa.accept_19_15_12_18_1_6634 15 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 31 265 (accept_3_3 14 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 31 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 31 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 265 (Polychromatic418967fa.accept_22_12_9_1_1_13113 12 31
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 265 (accept_3_3 11 31 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  31 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 265
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 265 (accept_3_3 8 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  265 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 31 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 265 (accept_3_3 5 31 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 31 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 265
  (Polychromatic418967fa.accept_21_3_10_13_1_16174 3 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 265 (accept_3_3 2 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31
  265 (Polychromatic418967fa.accept_17_1_14_10_1_10151 1 31 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 31 265))))))))))))))))))))))))))))))) (allB_succ 30 265 (allA_succ_of_accept 29 30 265
  (accept_3_3 29 30 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 265
  (Polychromatic418967fa.accept_9_1_3_4_1_47 28 30 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 30 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 265 (accept_3_3 26 30 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 30 265 5 5 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 30 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 30 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 265 (accept_3_3 23 30 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 30 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 30 265
  (Polychromatic418967fa.accept_16_5_14_9_1_2572 21 30 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 265 5 4 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 30 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 265 (accept_3_3 17 30 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 16
  30 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 265 5 3 6 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 265 (accept_3_3 14
  30 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 265
  (Polychromatic418967fa.accept_20_13_10_5_1_3338 13 30 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 30 265 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 30 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 265 (accept_3_3 11 30 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 30 265 5 2 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 30 265 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 30 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 265 (accept_3_3 8 30 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 30 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 30 265 5 1 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 30 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 30 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 265 (accept_3_3 2 30 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 30
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 265))))))))))))))))))))))))))))))
  (allB_succ 29 265 (allA_of_3_1 29 29 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 265
  (allA_succ_of_accept 27 28 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 265 (accept_3_3 26 28 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 28 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 24
  28 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 265 (accept_3_3 23 28
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 265
  (Polychromatic418967fa.accept_10_2_8_5_1_587 22 28 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 28 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 265 (accept_3_3 20 28 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 28 265 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 28 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 265
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 28 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 265 (accept_3_3 17 28 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  28 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 28 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 265 (accept_3_3 14 28 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 28 265 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 28 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 28 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 265 (accept_3_3 11 28 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 265 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 28 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 265 (accept_3_3 8 28 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 265
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 28 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 265 (accept_3_3 5 28 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  265 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 28 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 28 265 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 265 (accept_3_3 2 28 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 265 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 28 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 265)))))))))))))))))))))))))))) (allB_succ 27 265
  (allA_succ_of_accept 26 27 265 (accept_3_3 26 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  27 265 (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 27 265 (Polychromatic418967fa.accept_15_9_12_10_1_809 24 27 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 265 (accept_3_3 23 27 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 265
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 265 (accept_3_3 20 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 265 (Polychromatic418967fa.accept_13_6_1_5_1_3988 19 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 265 (accept_3_3 17 27 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 265
  (Polychromatic418967fa.accept_20_15_7_5_1_2115 15 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 265 (accept_3_3 14 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 265 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 265 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 27 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 265 (accept_3_3 11 27 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 265
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 265 (accept_3_3 8 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  265 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 265 (accept_3_3 5 27 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 265
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 265 (accept_3_3 2 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  265 (Polychromatic418967fa.accept_19_1_8_18_1_6667 1 27 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 265))))))))))))))))))))))))))) (allB_succ 26 265 (allA_of_3_1 26 26 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 265 (allA_succ_of_accept 24 25 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 24
  25 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 265 (accept_3_3 23 25
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 265
  (Polychromatic418967fa.accept_18_4_7_13_1_3303 22 25 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 25 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 25 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 265 5 4 5 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 25 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 265
  (Polychromatic418967fa.accept_21_18_4_13_1_5602 18 25 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 265 (accept_3_3 17 25 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 25 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 25 265 5 3 5 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 25 265 (accept_3_3 14 25 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 25 265 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 25 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 265 (accept_3_3 11 25 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 265 5 2 5 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 25
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 265 (accept_3_3 8 25 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 265 (Polychromatic418967fa.accept_13_7_12_5_1_1603
  7 25 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 265
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 25 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 265 5 1 5 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 265 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 25 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 265 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 25 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 265 (accept_3_3 2 25 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 25
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 265))))))))))))))))))))))))) (allB_succ
  24 265 (allA_succ_of_accept 23 24 265 (accept_3_3 23 24 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 265 (Polychromatic418967fa.accept_20_2_4_5_1_13401 22 24 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 265 (accept_3_3 20 24 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 19
  24 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 265
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 24 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 265 (accept_3_3 17 24 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 24 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 265 (Polychromatic418967fa.accept_16_15_8_9_1_2563 15 24 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 265 (accept_3_3 14 24 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 265 (Polychromatic418967fa.accept_19_13_5_18_1_8106 13 24
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 24 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 265 (accept_3_3 11 24 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 24 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 265 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 265 (accept_3_3 8 24 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 265 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 265
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 24 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 265 (accept_3_3 5 24 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  265 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 24 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 265 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 265 (accept_3_3 2 24 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 24 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 265)))))))))))))))))))))))) (allB_succ 23 265 (allA_of_3_1 23 23
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 265 (allA_succ_of_accept 21 22 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 265 (accept_3_3 20 22 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 265 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 22 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 265 (accept_3_3 17 22 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 265 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 22 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 265 (accept_3_3 14 22 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 22 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 265 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 22 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 265 (accept_3_3 11 22 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 265 (Polychromatic418967fa.accept_18_10_4_13_1_3296 10 22 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 265 (accept_3_3 8 22 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 265 (Polychromatic418967fa.accept_19_6_3_18_1_5262 6 22 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 265 (accept_3_3 5 22 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 265 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 22 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 265 (accept_3_3 2 22 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 265 (Polychromatic418967fa.accept_13_1_9_5_1_1598 1
  22 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 265)))))))))))))))))))))) (allB_succ
  21 265 (allA_succ_of_accept 20 21 265 (accept_3_3 20 21 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 21 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 265 (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 21
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 265 (accept_3_3 17 21 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  21 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 265 (accept_3_3 14 21 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 265 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 21 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 265 (accept_3_3 11 21 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 21 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 265
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 21 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 265 (accept_3_3 8 21 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  265 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 21 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 265 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 265 (accept_3_3 5 21 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 265 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  21 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 265 (accept_3_3 2 21 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 21
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 265))))))))))))))))))))) (allB_succ 20
  265 (allA_of_3_1 20 20 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 265 (allA_succ_of_accept 18 19 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 265 (accept_3_3 17 19 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 19 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 19 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 265 (accept_3_3 14 19 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 265 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 19 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 265
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 265 (accept_3_3 11 19 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 265 (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 19 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 265 (accept_3_3 8 19 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 265 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 265 (accept_3_3 5 19 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  265 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 19 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 265 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 19 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 265 (accept_3_3 2 19 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 19 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 265))))))))))))))))))) (allB_succ 18 265 (allA_succ_of_accept 17
  18 265 (accept_3_3 17 18 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 265
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 18 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 265 (accept_3_3 14 18 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 265 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 18 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 265 (Polychromatic418967fa.accept_7_5_4_6_1_167 12
  18 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 265 (accept_3_3 11 18
  265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 265
  (Polychromatic418967fa.accept_7_3_4_6_1_329 10 18 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 18 265 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 265 (accept_3_3 8 18 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 18 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 265 (Polychromatic418967fa.accept_11_6_7_1_1_564 6
  18 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 265 (accept_3_3 5 18 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 265
  (Polychromatic418967fa.accept_21_4_18_13_1_10435 4 18 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 18 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 265 (accept_3_3 2 18 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 18 265 (Polychromatic418967fa.accept_16_1_2_9_1_1607 1 18 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 265)))))))))))))))))) (allB_succ 17 265 (allA_of_3_1 17 17 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 265 (allA_succ_of_accept 15 16 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 265 (accept_3_3 14 16 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 265 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 16 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 16 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 265 (accept_3_3 11 16 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 16 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 265 (accept_3_3 8 16 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  265 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 16 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 16 265 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 16 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 265 (accept_3_3 5 16 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 265 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 16 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 265 (accept_3_3 2 16 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16
  265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 16 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 265)))))))))))))))) (allB_succ 15 265 (allA_succ_of_accept 14 15 265 (accept_3_3 14 15 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 265 (Polychromatic418967fa.accept_20_13_15_5_1_4628 13 15
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 265
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 15 265 (accept_3_3 11 15 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15
  265 5 2 3 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15
  265 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 15 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 265 (accept_3_3 8 15 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  265 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 15 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 265 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 15 265 5 1 3 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 265 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 265
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 15 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 265 (accept_3_3 2 15 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15
  265 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 15 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 265))))))))))))))) (allB_succ 14 265 (allA_of_3_1 14 14 265 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 13 265 (allA_succ_of_accept 12 13 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 13 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 13 265 (accept_3_3 11 13 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13 265 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 13
  265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 265
  (Polychromatic418967fa.accept_17_9_13_10_1_1825 9 13 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 13 265 (accept_3_3 8 13 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13
  265 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 13 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 13 265 (Polychromatic418967fa.accept_16_6_13_9_1_4690 6 13 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 265 (accept_3_3 5 13 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 13 265 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 13 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 265 (Polychromatic418967fa.accept_11_3_2_1_1_994 3
  13 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 265 (accept_3_3 2 13 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 265 (Polychromatic418967fa.accept_15_1_13_10_1_1507
  1 13 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 265))))))))))))) (allB_succ 12 265
  (allA_succ_of_accept 11 12 265 (accept_3_3 11 12 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  12 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 12 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 265 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 12 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 265 (accept_3_3 8 12 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 265 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 265
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 12 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 265 (accept_3_3 5 12 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12
  265 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 12 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 12 265 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 12 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 265 (accept_3_3 2 12 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 12 265 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 265)))))))))))) (allB_succ 11 265 (allA_of_3_1 11 11 265
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 265 (allA_succ_of_accept 9 10 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 265 (accept_3_3 8 10 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  265 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 265 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 10 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 10 265 5 1 2 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 10 265 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 10 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 265
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 10 265 (accept_3_3 2 10 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10
  265 (Polychromatic418967fa.accept_16_1_10_9_1_4645 1 10 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 10 265)))))))))) (allB_succ 9 265 (allA_succ_of_accept 8 9 265 (accept_3_3 8 9 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 265 (Polychromatic418967fa.accept_20_7_9_5_1_292 7 9 265
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 265
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 9 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 265 (accept_3_3 5 9 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 265
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 265 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 9 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 265 (accept_3_3 2 9 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 265 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 9 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 265))))))))) (allB_succ 8 265 (allA_of_3_1 8 8 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 265 (allA_succ_of_accept 6 7 265
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 265 (accept_3_3 5 7 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 265
  (Polychromatic418967fa.accept_15_4_7_10_1_807 4 7 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 265 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 7 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 265 (accept_3_3 2 7 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 265 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 265))))))) (allB_succ 6 265 (allA_succ_of_accept 5 6 265
  (accept_3_3 5 6 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 265
  (Polychromatic418967fa.accept_10_4_6_5_1_74 4 6 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 265 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 265 (accept_3_3 2 6 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 265 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 6 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 265)))))) (allB_succ 5 265 (allA_of_3_1 5 5 265 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 265 (allA_succ_of_accept 3 4 265
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 265 (accept_3_3 2 4 265 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 265
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 4 265 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 265)))) (allB_succ 3 265 (allA_succ_of_accept 2 3 265 (accept_3_3 2 3 265 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 265 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 3 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 265))) (allB_succ 2 265 (allA_of_3_1 2 2 265 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  265)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


