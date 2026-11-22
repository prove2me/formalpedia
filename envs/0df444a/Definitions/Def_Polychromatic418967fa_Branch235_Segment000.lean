-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch235_Segment000
-- name    : Polychromatic418967fa_Branch235_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:37:21.075597+00:00
-- url     : https://prove2.me/theorems/bb201d4f-ce99-4225-8acf-321c82430933
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

def Polychromatic418967fa.branch_235_segment_000 : allB 123 235 :=
  allB_succ' 114 122 235 (Eq.refl Bool.true) (allA_of_3_1 114 122 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 115 121 235 (Eq.refl Bool.true) (allA_succ_of_accept 114 121 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 114 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 121 235 (accept_3_3 113 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 121 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 112 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 121 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 111 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 121 235 (accept_3_3 110 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 121 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 109 121
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 121 235
  (Polychromatic418967fa.accept_26_4_17_1_1_14108 108 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 121 235 (accept_3_3 107 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 121 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 105 121
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 121 235 (accept_3_3 104 121
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 121 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 103 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 121 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 235 (accept_3_3 101 121 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 121 235 (Polychromatic418967fa.accept_14_2_9_11_1_3054 100 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 235
  (Polychromatic418967fa.accept_10_9_1_5_1_594 99 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 235 (accept_3_3 98 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 97 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 235 (accept_3_3 95 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 93 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 235 (accept_3_3 92 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 235 (Polychromatic418967fa.accept_21_7_16_4_1_9713 91 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 235 (accept_3_3 89 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 87 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 235 (accept_3_3 86 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 235 (Polychromatic418967fa.accept_16_5_9_11_1_3762 85 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 235 (accept_3_3 83 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 235
  (Polychromatic418967fa.accept_13_3_4_1_1_363 81 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 235 (accept_3_3 80 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 235 (accept_3_3 77 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 235 (accept_3_3 74 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 73 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 235 (Polychromatic418967fa.accept_14_2_9_11_1_3054 72 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 235 (accept_3_3 71 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 121 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 235 (accept_3_3 68 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 67 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 235 (accept_3_3 65 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 64 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 235
  (Polychromatic418967fa.accept_25_13_21_10_1_14107 63 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 121 235 (accept_3_3 62 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 121 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 121 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 121 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 235 (accept_3_3 59 121 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 235 (accept_3_3 56 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 235 (accept_3_3 53 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 235 (accept_3_3 50 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 235 (accept_3_3 47 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 235
  (Polychromatic418967fa.accept_20_5_1_15_1_3928 45 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 235 (accept_3_3 44 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 235 (accept_3_3 41 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 235 (accept_3_3 38 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 235 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 235 (accept_3_3 35 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 235 (accept_3_3 32 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 235 (Polychromatic418967fa.accept_13_5_4_1_1_364 31 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 235 (accept_3_3 29 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 121 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 235 (accept_3_3 26 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 235 (accept_3_3 23 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 235 (accept_3_3 20 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 235 (accept_3_3 17 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 235 (accept_3_3 14 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 235 (accept_3_3 11 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 235
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 235 (accept_3_3 8 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 235 (accept_3_3 5 121 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 121 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 235 (accept_3_3 2 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 235 (Polychromatic418967fa.accept_22_1_11_15_1_6075 1 121 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 120 235 (Eq.refl Bool.true) (allA_succ_of_gcd 115 120 235 5 23 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 114 120 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 114 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 120 235 (accept_3_3 113 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 120 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 112 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 120 235 (Polychromatic418967fa.accept_13_7_3_1_1_814 111 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 120 235 5 22 24 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 235
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 109 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 120 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 108 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 235 (accept_3_3 107 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 120 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 106 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 120 235 5 21 24 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 120 235 (accept_3_3 104 120 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 120 235 (Polychromatic418967fa.accept_7_5_1_4_1_122
  103 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 120 235
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 102 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 120 235 (accept_3_3 101 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 120 235 5 20 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 120 235 (Polychromatic418967fa.accept_16_3_8_11_1_2714 99 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 120 235 (accept_3_3 98 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 120 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 97 120 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 120 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 96 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 95 120 235 5 19 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 94 120 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 94 120 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 235
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 93 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 120 235 (accept_3_3 92 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 120 235 (Polychromatic418967fa.accept_22_3_10_15_1_9511 91 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 120 235 5 18 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 120 235 (accept_3_3 89 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 120 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 120 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 235 (accept_3_3 86 120 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 120 235 5 17 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 120 235
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 84 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 120 235 (accept_3_3 83 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 120 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 120 235 (Polychromatic418967fa.accept_17_13_1_14_1_1149 81 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 120 235 5 16 24 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 120 235
  (Polychromatic418967fa.accept_9_7_3_1_1_386 79 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 120 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 78 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 235 (accept_3_3 77 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 120 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 120 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 120 235 5 15 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 120 235 (accept_3_3 74 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 120 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 120 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 120 235
  (Polychromatic418967fa.accept_13_7_3_1_1_814 72 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 120 235 (accept_3_3 71 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  120 235 5 14 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 120 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 235 (accept_3_3 68 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 120 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 120 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 120 235 (Polychromatic418967fa.accept_7_3_1_4_1_121
  66 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 120 235 5 13 24 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 120 235
  (Polychromatic418967fa.accept_17_13_1_14_1_1149 64 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 120 235 (Polychromatic418967fa.accept_13_11_3_1_1_1397 63 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 235 (accept_3_3 62 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 120 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 235 5 12 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 235 (accept_3_3 59
  120 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 235
  (Polychromatic418967fa.accept_9_4_3_1_1_154 58 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 120 235 (Polychromatic418967fa.accept_13_5_3_1_1_1398 57 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 235 (accept_3_3 56 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 120 235 5 11 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 120 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 120 235 (accept_3_3 53 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 120 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 120 235 5 10 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 120 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 235
  (Polychromatic418967fa.accept_21_6_15_4_1_5021 48 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 120 235 (accept_3_3 47 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 120 235 (Polychromatic418967fa.accept_13_7_3_1_1_814 46 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 120 235 5 9 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 120 235 (accept_3_3 44 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 120 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 120 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 120 235 (accept_3_3 41 120 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 235 5 8 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 235
  (Polychromatic418967fa.accept_18_3_12_1_1_3787 39 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 120 235 (accept_3_3 38 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 120 235 (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 120 235 (Polychromatic418967fa.accept_16_4_8_11_1_5961 36 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 120 235 5 7 24 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 120 235
  (Polychromatic418967fa.accept_9_7_3_1_1_386 34 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 120 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 235 (accept_3_3 32 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 120 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 120 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 235 5 6 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 235 (accept_3_3 29 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 235 (Polychromatic418967fa.accept_13_2_3_1_1_3823 28 120
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 235
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 120 235 (accept_3_3 26 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  120 235 5 5 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 120 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 120 235 (accept_3_3 23 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 120 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 235 (Polychromatic418967fa.accept_16_5_8_11_1_9582 21 120
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 235 5 4 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 120 235 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 235 (accept_3_3 17 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 120 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 120 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 235 5 3 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 235 (accept_3_3 14 120 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 120 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 120 235 (accept_3_3 11 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  120 235 5 2 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 120 235 (Polychromatic418967fa.accept_21_9_15_4_1_2190 9 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 120 235 (accept_3_3 8 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 120 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 120 235 5 1 24 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 120 235
  (Polychromatic418967fa.accept_9_4_3_1_1_154 4 120 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 120 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 235 (accept_3_3 2 120 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 120 235 (Polychromatic418967fa.accept_19_1_6_7_1_2019 1 120 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 119 235 (Eq.refl Bool.true) (allA_of_3_1 117 119 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 118 235 (allA_succ_of_accept 117 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 118 235 (accept_3_3 116 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 118 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 115 118
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 118 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 114 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 118 235 (accept_3_3 113 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 118 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 112 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 118 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 118 235 (accept_3_3 110 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 109 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 118 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 108 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 118 235 (accept_3_3 107 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 118 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 106 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 118 235 (accept_3_3 104 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 118 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 103 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 118 235
  (Polychromatic418967fa.accept_10_2_8_5_1_587 102 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 118 235 (accept_3_3 101 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 118 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 100 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 118 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 118 235 (accept_3_3 98 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 118 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 96 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 118 235 (accept_3_3 95 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 118 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 94 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 118 235 (accept_3_3 92 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 118 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 91 118 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 118 235
  (Polychromatic418967fa.accept_19_14_4_7_1_8728 90 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 118 235 (accept_3_3 89 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 118 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 118 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 118 235 (accept_3_3 86 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 118 235
  (Polychromatic418967fa.accept_11_7_8_4_1_718 84 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 118 235 (accept_3_3 83 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 118 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 82 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 118 235 (accept_3_3 80 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 118 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 118 235
  (Polychromatic418967fa.accept_11_1_8_4_1_717 78 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 118 235 (accept_3_3 77 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 118 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 118 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 235 (accept_3_3 74 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 118 235 (accept_3_3 71 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 118 235 (Polychromatic418967fa.accept_17_2_16_14_1_2116 70 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 235 (accept_3_3 68 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 67 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 235 (accept_3_3 65 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 235 (accept_3_3 62 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 235
  (Polychromatic418967fa.accept_19_3_4_7_1_987 60 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 235 (accept_3_3 59 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 235 (accept_3_3 56 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 235 (Polychromatic418967fa.accept_24_7_22_19_1_14106 55 118 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 235 (accept_3_3 53 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 235 (accept_3_3 50 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 235
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 48 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 118 235 (accept_3_3 47 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 118 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 46 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 235 (accept_3_3 44
  118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 235
  (Polychromatic418967fa.accept_10_3_8_5_1_606 43 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 118 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 118 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 118 235 (accept_3_3 41 118 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 118 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 118 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39
  118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 235 (accept_3_3 38
  118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 118 235 (Polychromatic418967fa.accept_16_4_6_11_1_3753 36 118 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 118 235 (accept_3_3 35 118 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 118 235 (Polychromatic418967fa.accept_11_1_8_4_1_717 34 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 118 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 118 235 (accept_3_3 32 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 118 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 118 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 118 235 (accept_3_3 29 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 118 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 118 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 118 235 (accept_3_3 26 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 118 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 118 235 (accept_3_3 23 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 118 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 118 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 118 235 (accept_3_3 20 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 118 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 118 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 235 (accept_3_3 17 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 118 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 118 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 118 235 (accept_3_3 14 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 118 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 235 (accept_3_3 11 118 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 118 235 (accept_3_3 8 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  118 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 118 235 (Polychromatic418967fa.accept_21_6_13_4_1_6521 6 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 235 (accept_3_3 5 118 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 118 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 118 235 (accept_3_3 2 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  118 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 118
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 235 (allA_succ_of_accept 116 117 235 (accept_3_3 116 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 235 (Polychromatic418967fa.accept_27_7_9_19_1_14105 115 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 235 (Polychromatic418967fa.accept_4_2_1_3_1_27
  114 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 235 (accept_3_3
  113 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 112 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 117 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 111 117 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 235 (accept_3_3 110 117 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 117 235 (Polychromatic418967fa.accept_19_14_3_7_1_7248 109 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 235
  (Polychromatic418967fa.accept_10_8_7_5_1_602 108 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 117 235 (accept_3_3 107 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 117 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 117 235 (Polychromatic418967fa.accept_16_9_5_11_1_3776 105 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 235 (accept_3_3 104 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 103 117
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 117 235 (accept_3_3 101 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 117 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 117 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 99 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 235 (accept_3_3 98 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 97 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 235
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 96 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 117 235 (accept_3_3 95 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 117 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 117 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 235 (accept_3_3 92 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 235 (Polychromatic418967fa.accept_11_3_7_4_1_1133 91 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 117 235 (accept_3_3 89 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 117 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 117 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 87 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 235 (accept_3_3 86 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 117 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 235
  (Polychromatic418967fa.accept_15_9_12_10_1_809 84 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 117 235 (accept_3_3 83 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 117 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 117 235 (Polychromatic418967fa.accept_15_6_12_10_1_1543 81 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 235 (accept_3_3 80 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 117 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 117 235 (accept_3_3 77 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 117 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 117 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 75 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 235 (accept_3_3 74 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 73 117
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 72 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 117 235 (accept_3_3 71 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 117 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 117 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 235 (accept_3_3 68 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 235 (Polychromatic418967fa.accept_15_7_12_10_1_4335 67 117 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 117 235 (accept_3_3 65 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 117 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 117 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 235 (accept_3_3 62 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 235 (Polychromatic418967fa.accept_19_4_3_7_1_5876 61 117
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 235
  (Polychromatic418967fa.accept_18_6_9_1_1_3769 60 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 117 235 (accept_3_3 59 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 117 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 117 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 235 (accept_3_3 56 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 117 235 (accept_3_3 53 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 117 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 117 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 235 (accept_3_3 50 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 235 (Polychromatic418967fa.accept_21_7_12_4_1_6493 49 117 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 117 235 (accept_3_3 47 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 117 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 117 235 (Polychromatic418967fa.accept_20_5_17_15_1_6858 45 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 235 (accept_3_3 44 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 117 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 235 (accept_3_3 41 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 117 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 235 (accept_3_3 38 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 117 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 117 235 (accept_3_3 35 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 117 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 235 (accept_3_3 32 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 235 (Polychromatic418967fa.accept_19_12_3_7_1_5832 31 117
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 117 235 (accept_3_3 29 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 117 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 235 (accept_3_3 26 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 235 (Polychromatic418967fa.accept_11_3_7_4_1_1133 25 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 235
  (Polychromatic418967fa.accept_15_9_12_10_1_809 24 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 235 (accept_3_3 23 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 235 (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 235 (accept_3_3 20 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 235 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 117
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 235 (accept_3_3 17 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 235 (accept_3_3 14 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 235
  (Polychromatic418967fa.accept_10_2_7_5_1_605 12 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 235 (accept_3_3 11 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 235 (accept_3_3 8 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 235 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 235 (accept_3_3 5 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 235 (accept_3_3 2 117 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 117 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 235 (allA_of_3_1 116 116 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 235
  (allA_succ_of_accept 114 115 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 114 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 235 (accept_3_3 113 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 115 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 112 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 111 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 115 235 5 22 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 115 235 (Polychromatic418967fa.accept_11_10_5_4_1_711 109 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 115 235
  (Polychromatic418967fa.accept_19_13_1_7_1_5906 108 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 115 235 (accept_3_3 107 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 115 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 106 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 115 235 5 21 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 115 235 (accept_3_3 104 115 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 115 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 103 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 102 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 115 235 (accept_3_3 101 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  100 115 235 5 20 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 99 115 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 99 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 115 235 (accept_3_3 98 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 115 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 97 115 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 115 235 (Polychromatic418967fa.accept_9_6_7_1_1_145
  96 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 115 235 5 19 23 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 115 235
  (Polychromatic418967fa.accept_9_4_7_1_1_379 94 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 115 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 93 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 115 235 (accept_3_3 92 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 115 235 (Polychromatic418967fa.accept_14_7_3_11_1_2199 91 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 115 235 5 18 23 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 115 235 (accept_3_3 89 115 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 235
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 88 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 115 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 87 115 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 115 235 (accept_3_3 86 115 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 85 115 235 5 17 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 115 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 84 115 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 235 (accept_3_3 83 115 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 235 (Polychromatic418967fa.accept_19_6_1_7_1_5872
  82 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 235
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 81 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 115 235 5 16 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 115 235 (Polychromatic418967fa.accept_16_15_3_11_1_5997 79 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 115 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 78 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 115 235 (accept_3_3 77 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 115 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 115 235 5 15 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 115 235 (accept_3_3 74 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 115 235 (Polychromatic418967fa.accept_13_8_11_1_1_3789 73 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 235 (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 115
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 235 (accept_3_3 71 115
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 115 235 5 14 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 115 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 235 (accept_3_3 68 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 115 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 115 235 5 13 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 115 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 64 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 115 235 (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 235 (accept_3_3 62 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 115 235 (Polychromatic418967fa.accept_13_9_11_1_1_1375 61 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 115 235 5 12 23 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 115 235 (accept_3_3 59 115 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 235 (Polychromatic418967fa.accept_9_4_7_1_1_379
  58 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 235 (accept_3_3 56 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  115 235 5 11 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 115 235 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 235 (accept_3_3 53 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 115 235 (Polychromatic418967fa.accept_17_1_13_14_1_478 52 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 51 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 115 235 5 10 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 115 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 115 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 235 (Polychromatic418967fa.accept_7_6_3_4_1_294
  48 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 235 (accept_3_3 47
  115 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 235
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 46 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 115 235 5 9 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 115 235 (accept_3_3 44 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 115 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 235 (accept_3_3 41 115 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 115 235 5 8 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 115 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 115 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 235 (accept_3_3 38 115 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 235
  (Polychromatic418967fa.accept_19_18_1_7_1_14104 37 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 115 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 115 235 5 7 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 115 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 115 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 235 (accept_3_3 32 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 115 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 115 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 115 235 5 6 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 115 235 (accept_3_3 29 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 235 (Polychromatic418967fa.accept_31_28_22_18_1_14103 28
  115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 235 (accept_3_3 26 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  115 235 5 5 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 115 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 115 235 (accept_3_3 23 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 115 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 115 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 115 235 5 4 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 235
  (Polychromatic418967fa.accept_21_19_10_4_1_14102 19 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 235 (Polychromatic418967fa.accept_17_1_13_14_1_478 18 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 235 (accept_3_3 17 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 235 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 115
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 235 5 3 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 235 (accept_3_3 14
  115 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 115 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 235 (accept_3_3 11 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 115 235 5 2 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 115 235 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 235 (accept_3_3 8 115 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 235 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 115
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 115 235 5 1 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 115 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 115 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 115 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 235 (accept_3_3 2 115 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  115 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 235 (allA_succ_of_accept 113 114 235 (accept_3_3 113 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 114 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 112 114 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 114 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 111 114
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 235 (accept_3_3 110 114
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 114 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 114 235 (Polychromatic418967fa.accept_13_4_10_1_1_1390 108 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 235 (accept_3_3 107 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 106 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 114 235 (accept_3_3 104 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 114 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 103 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 114 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 102 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 235 (accept_3_3 101 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 235 (Polychromatic418967fa.accept_13_9_10_1_1_1389 100
  114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 235
  (Polychromatic418967fa.accept_10_9_4_5_1_616 99 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 114 235 (accept_3_3 98 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 114 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 235 (accept_3_3 95 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 94 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 114 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 114 235 (accept_3_3 92 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 114 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 91 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 114 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 114 235 (accept_3_3 89 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 88 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 235
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 87 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 114 235 (accept_3_3 86 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 114 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 84 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 114 235 (accept_3_3 83 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 114 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 114 235 (accept_3_3 80 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 114 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 114 235 (Polychromatic418967fa.accept_15_3_9_10_1_2325 78 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 114 235 (accept_3_3 77 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 114 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 114 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 114 235 (accept_3_3 74 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 114 235 (Polychromatic418967fa.accept_15_12_9_10_1_2326 72 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 114 235 (accept_3_3 71 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 114 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 114 235 (accept_3_3 68 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 114 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 114 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 114 235 (accept_3_3 65 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 235 (Polychromatic418967fa.accept_15_4_9_10_1_5384 64 114 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 114 235
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 63 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 114 235 (accept_3_3 62 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 114 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 235 (Polychromatic418967fa.accept_17_9_12_14_1_5423 60 114
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 114 235 (accept_3_3 59 114
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 58 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 114 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 235 (accept_3_3 56 114 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 114 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 235 (Polychromatic418967fa.accept_7_5_2_4_1_126
  54 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 235 (accept_3_3 53
  114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 235
  (Polychromatic418967fa.accept_9_7_6_1_1_709 52 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 114 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 114 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 235 (accept_3_3 50 114 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 235 (Polychromatic418967fa.accept_7_6_2_4_1_291
  48 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 235 (accept_3_3 47
  114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 235
  (Polychromatic418967fa.accept_10_6_4_5_1_615 46 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 235 (accept_3_3 44 114 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 114 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 235
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 42 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 114 235 (accept_3_3 41 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 114 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 114 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 114 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 235 (accept_3_3 38 114 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 235
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 114 235 (accept_3_3 35 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 114 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 235 (accept_3_3 32 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 235 (accept_3_3 29 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 114 235 (Polychromatic418967fa.accept_17_11_12_14_1_5431 28 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 235 (accept_3_3 26 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 235
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 24 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 114 235 (accept_3_3 23 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 114 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 235 (accept_3_3 20 114 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 235 (Polychromatic418967fa.accept_7_5_2_4_1_126
  19 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 235
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 235 (accept_3_3 17 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 114 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 235 (Polychromatic418967fa.accept_17_15_12_14_1_2087 15 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 235 (accept_3_3 14 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 235 (accept_3_3 11 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 114 235 (Polychromatic418967fa.accept_20_10_14_15_1_9885 10 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 235 (accept_3_3 8 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 114 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 235 (accept_3_3 5 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  114 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 114 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 235 (accept_3_3 2 114 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 235 (allA_of_3_1 113 113 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 235
  (allA_succ_of_accept 111 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 112 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 112 235 (accept_3_3 110 112 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 112 235 (Polychromatic418967fa.accept_13_5_8_1_1_2161 109 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 112 235
  (Polychromatic418967fa.accept_10_8_2_5_1_596 108 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 112 235 (accept_3_3 107 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 106 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 112 235 (accept_3_3 104 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 112 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 103 112 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 112 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 102 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 112 235 (accept_3_3 101 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 112 235 (Polychromatic418967fa.accept_13_9_8_1_1_824 100 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 112 235 (accept_3_3 98 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 97 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 112 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 96 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 112 235 (accept_3_3 95 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 112 235 (Polychromatic418967fa.accept_11_6_2_4_1_1703 94 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 112 235 (accept_3_3 92 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 112 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 91 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 112 235
  (Polychromatic418967fa.accept_13_12_8_1_1_825 90 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 112 235 (accept_3_3 89 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 112 235 (accept_3_3 86 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 112 235 (Polychromatic418967fa.accept_13_7_8_1_1_2145 85 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 112 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 112 235 (accept_3_3 83 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 112 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 112 235 (accept_3_3 80 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 112 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 78 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 112 235 (accept_3_3 77 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 112 235 (Polychromatic418967fa.accept_13_11_8_1_1_3815 76 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 112 235 (accept_3_3 74 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 112 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 73 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 112 235
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 72 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 112 235 (accept_3_3 71 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 112 235 (accept_3_3 68 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 112 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 67 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 112 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 112 235 (accept_3_3 65 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 112 235 (Polychromatic418967fa.accept_11_9_2_4_1_707 64 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 112 235 (accept_3_3 62 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 112 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 112 235 (accept_3_3 59 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 112 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 112 235 (accept_3_3 56 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 112 235 (Polychromatic418967fa.accept_21_13_7_4_1_4991 55 112 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 112 235
  (Polychromatic418967fa.accept_19_16_17_7_1_5845 54 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 112 235 (accept_3_3 53 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 112 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 112 235 (accept_3_3 50 112 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 112 235 (Polychromatic418967fa.accept_15_4_7_10_1_807
  49 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 112 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 112 235 (accept_3_3 47 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 112 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 112 235 (accept_3_3 44 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 112 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 112 235 (accept_3_3 41 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 112 235 (Polychromatic418967fa.accept_19_2_17_7_1_8735 40 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 112 235 (accept_3_3 38 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 112 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 235
  (Polychromatic418967fa.accept_23_13_20_5_1_9197 36 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 112 235 (accept_3_3 35 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 112 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 112 235 (accept_3_3 32 112 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 112 235 (Polychromatic418967fa.accept_11_9_2_4_1_707
  31 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 112 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 112 235 (accept_3_3 29 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 112 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 235 (accept_3_3 26 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 112 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 112 235 (accept_3_3 23 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 112 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 112 235 (accept_3_3 20 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 112 235 (Polychromatic418967fa.accept_13_6_8_1_1_2913 19 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 235
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 112 235 (accept_3_3 17 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 235 (accept_3_3 14 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 112 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 112 235 (accept_3_3 11 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 112 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 235 (accept_3_3 8 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 235 (accept_3_3 5 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 235 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 112 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 235 (accept_3_3 2 112 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 112 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 235 (allA_succ_of_accept 110 111 235 (accept_3_3 110 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 109 111 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 108 111
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 235 (accept_3_3 107 111
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 106 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 111 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 105 111 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 235 (accept_3_3 104 111 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 111 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 103 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 235
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 102 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 111 235 (accept_3_3 101 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 111 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 111 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 99 111
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 235 (accept_3_3 98 111
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 235
  (Polychromatic418967fa.accept_9_7_3_1_1_386 97 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 111 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 111 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 235 (accept_3_3 95 111 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 111 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 93
  111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 235 (accept_3_3 92
  111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 235
  (Polychromatic418967fa.accept_15_1_6_10_1_23 91 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 111 235 (Polychromatic418967fa.accept_16_10_15_11_1_3785 90 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 235 (accept_3_3 89 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 111 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 87 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 111 235 (accept_3_3 86 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 111 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 85 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 111 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 235 (accept_3_3 83 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 111 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 111 235 (accept_3_3 80 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 111 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 111 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 78 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 235 (accept_3_3 77 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 111 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 111 235 (accept_3_3 74 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 111 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 111 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 235 (accept_3_3 71 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 69 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 111 235 (accept_3_3 68 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 111 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 111 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 235 (accept_3_3 65 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 111 235
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 111 235 (accept_3_3 62 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 111 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 111 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 235 (accept_3_3 59 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 111 235 (accept_3_3 56 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 111 235 (Polychromatic418967fa.accept_13_3_7_1_1_334 55 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 111 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 235 (accept_3_3 53 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 111 235 (accept_3_3 50 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 111 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 111 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539 48 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 235 (accept_3_3 47 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 111 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 111 235 (accept_3_3 44 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 111 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 111 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 235 (accept_3_3 41 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 235
  (Polychromatic418967fa.accept_10_9_1_5_1_594 39 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 111 235 (accept_3_3 38 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 111 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 111 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 235 (accept_3_3 35 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 111 235 (accept_3_3 32 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 111 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 111 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 235 (accept_3_3 29 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 235
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 235 (accept_3_3 26 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 111 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 111 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 235 (accept_3_3 23 111 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 235 (accept_3_3 20 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 111 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 235 (accept_3_3 17 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 235 (accept_3_3 14 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 235 (accept_3_3 11 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 235 (accept_3_3 8 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 235 (accept_3_3 5 111 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 235 (accept_3_3 2 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 1 111 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 235 (allA_of_3_1 110 110 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 235
  (allA_succ_of_accept 108 109 235 (Polychromatic418967fa.accept_13_4_5_1_1_833 108 109 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 235 (accept_3_3 107 109 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 235
  (Polychromatic418967fa.accept_19_10_14_7_1_11440 105 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 109 235 (accept_3_3 104 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 109 235 (Polychromatic418967fa.accept_13_12_5_1_1_1383 103 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27
  102 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 235 (accept_3_3
  101 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 235
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 100 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 109 235 (Polychromatic418967fa.accept_13_8_5_1_1_1381 99 109 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 109 235 (accept_3_3 98 109 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 109 235 (Polychromatic418967fa.accept_13_6_5_1_1_834 97 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 109 235
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 96 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 109 235 (accept_3_3 95 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 109 235 (Polychromatic418967fa.accept_11_5_10_4_1_1157 93 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 109 235 (accept_3_3 92 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 109 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 91 109 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 109 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 109 235 (accept_3_3 89 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 109 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 88 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 109 235 (Polychromatic418967fa.accept_13_9_5_1_1_1382 87 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 109 235 (accept_3_3 86 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 109 235 (Polychromatic418967fa.accept_20_5_9_15_1_3973 85 109
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 109 235
  (Polychromatic418967fa.accept_10_4_9_5_1_84 84 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 109 235 (accept_3_3 83 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 109 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 81 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 109 235 (accept_3_3 80 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 109 235 (Polychromatic418967fa.accept_19_3_14_7_1_7204 79 109 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 109 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 109 235 (accept_3_3 77 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 109 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 76 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 109 235 (Polychromatic418967fa.accept_19_18_14_7_1_5864 75 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 109 235 (accept_3_3 74 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 109 235 (Polychromatic418967fa.accept_13_8_5_1_1_1381 73 109
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 235
  (Polychromatic418967fa.accept_16_8_13_11_1_4772 72 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 109 235 (accept_3_3 71 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 109 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 235 (Polychromatic418967fa.accept_13_4_5_1_1_833 69 109
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 235 (accept_3_3 68 109
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 235
  (Polychromatic418967fa.accept_15_7_4_10_1_1513 67 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 109 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 235 (accept_3_3 65 109 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 109 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 64 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 235
  (Polychromatic418967fa.accept_19_6_14_7_1_5902 63 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 235 (accept_3_3 62 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 61 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 235 (Polychromatic418967fa.accept_11_5_10_4_1_1157 60 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 235 (accept_3_3 59 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 109 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 235
  (Polychromatic418967fa.accept_17_6_7_14_1_6704 57 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 235 (accept_3_3 56 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 235 (Polychromatic418967fa.accept_13_3_5_1_1_2144 55 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 235 (accept_3_3 53 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 235 (Polychromatic418967fa.accept_15_7_4_10_1_1513 52 109 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 235
  (Polychromatic418967fa.accept_10_1_9_5_1_83 51 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 235 (accept_3_3 50 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 235 (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 235 (Polychromatic418967fa.accept_13_9_5_1_1_1382 48 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 235 (accept_3_3 47 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 235
  (Polychromatic418967fa.accept_13_6_5_1_1_834 45 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 235 (accept_3_3 44 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 235 (Polychromatic418967fa.accept_13_4_5_1_1_833 43 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 235 (accept_3_3 41 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 235 (Polychromatic418967fa.accept_16_8_13_11_1_4772 40 109 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 235
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 39 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 235 (accept_3_3 38 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 235 (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 235 (accept_3_3 35 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 235
  (Polychromatic418967fa.accept_22_11_21_15_1_7853 33 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 109 235 (accept_3_3 32 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 109 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 109 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 235 (accept_3_3 29 109 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 235
  (Polychromatic418967fa.accept_15_13_4_10_1_821 28 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 109 235 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 109 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 235 (accept_3_3 26 109 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 109 235 (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 235
  (Polychromatic418967fa.accept_10_4_9_5_1_84 24 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 235 (accept_3_3 23 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 235 (accept_3_3 20 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 235 (Polychromatic418967fa.accept_13_6_5_1_1_834 19 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 235 (accept_3_3 17 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 235 (Polychromatic418967fa.accept_19_15_14_7_1_2044 15 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 235 (accept_3_3 14 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 109
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 235
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 235 (accept_3_3 11 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 235 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 235 (accept_3_3 8 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 235 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 235 (accept_3_3 5 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 109 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 235 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 235 (accept_3_3 2 109 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 109 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 235 (allA_succ_of_accept 107 108 235 (accept_3_3 107 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 108 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 106 108 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 235 (Polychromatic418967fa.accept_14_7_10_11_1_8112 105
  108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 235 (accept_3_3 104
  108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 108 235
  (Polychromatic418967fa.accept_8_7_4_3_1_156 103 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 108 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 102 108 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 235 (accept_3_3 101 108 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 108 235 (Polychromatic418967fa.accept_16_4_12_11_1_2650 100 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 99 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 108 235 (accept_3_3 98 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 108 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 97 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 108 235 (Polychromatic418967fa.accept_13_5_4_1_1_364 96 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 108 235 (accept_3_3 95 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 235 (Polychromatic418967fa.accept_13_3_4_1_1_363 94 108
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 235
  (Polychromatic418967fa.accept_10_3_8_5_1_606 93 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 108 235 (accept_3_3 92 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 108 235 (Polychromatic418967fa.accept_14_7_10_11_1_8112 91 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 108 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 108 235 (accept_3_3 89 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 235 (Polychromatic418967fa.accept_13_10_4_1_1_2142 88 108 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 235
  (Polychromatic418967fa.accept_8_7_4_3_1_156 87 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 108 235 (accept_3_3 86 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 108 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 108 235 (Polychromatic418967fa.accept_15_9_3_10_1_2312 84 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 235 (accept_3_3 83 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 82 108
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 235
  (Polychromatic418967fa.accept_13_3_4_1_1_363 81 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 108 235 (accept_3_3 80 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 108 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 108 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 235 (accept_3_3 77 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 235
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 75 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 108 235 (accept_3_3 74 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 108 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 73 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 108 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 235 (accept_3_3 71 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 235 (Polychromatic418967fa.accept_13_5_4_1_1_364 70 108
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 108 235 (accept_3_3 68 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 108 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 67 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 108 235 (Polychromatic418967fa.accept_15_6_3_10_1_2341 66 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 108 235 (accept_3_3 65 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 108 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 235
  (Polychromatic418967fa.accept_8_7_4_3_1_156 63 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 108 235 (accept_3_3 62 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 108 235 (Polychromatic418967fa.accept_19_4_13_7_1_4433 61 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 108 235 (Polychromatic418967fa.accept_19_3_13_7_1_7245 60 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 108 235 (accept_3_3 59 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 235 (Polychromatic418967fa.accept_15_13_3_10_1_2296 58 108
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 108 235 (accept_3_3 56 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 108 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 108 235 (Polychromatic418967fa.accept_15_9_3_10_1_2312 54 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 235 (accept_3_3 53 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 52 108
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 235
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 51 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 108 235 (accept_3_3 50 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 108 235 (Polychromatic418967fa.accept_13_10_4_1_1_2142 49 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 108 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 235 (accept_3_3 47 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 235 (Polychromatic418967fa.accept_11_2_9_4_1_310 46 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 235
  (Polychromatic418967fa.accept_20_5_8_15_1_9845 45 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 108 235 (accept_3_3 44 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 108 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 108 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 235 (accept_3_3 41 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 235 (Polychromatic418967fa.accept_16_8_12_11_1_3697 40 108
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 235
  (Polychromatic418967fa.accept_8_7_4_3_1_156 39 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 108 235 (accept_3_3 38 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 108 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 108 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 235 (accept_3_3 35 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 235
  (Polychromatic418967fa.accept_10_3_8_5_1_606 33 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 235 (accept_3_3 32 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 108 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 108 235 (Polychromatic418967fa.accept_19_11_13_7_1_5862 30 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 235 (accept_3_3 29 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 235 (Polychromatic418967fa.accept_15_13_3_10_1_2296 28 108
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 108 235 (accept_3_3 26 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 108 235 (Polychromatic418967fa.accept_17_8_6_14_1_6718 25 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 108 235 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 235 (accept_3_3 23 108 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 108 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 235
  (Polychromatic418967fa.accept_14_7_10_11_1_8112 21 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 108 235 (accept_3_3 20 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 235 (Polychromatic418967fa.accept_25_19_8_10_1_14101 19 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 235 (Polychromatic418967fa.accept_13_5_4_1_1_364
  18 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 235 (accept_3_3 17
  108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 235
  (Polychromatic418967fa.accept_13_3_4_1_1_363 16 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 108 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 108 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 235 (accept_3_3 14 108 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 108 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 235 (Polychromatic418967fa.accept_10_2_8_5_1_587
  12 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 235 (accept_3_3 11
  108 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 235
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 108 235 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 108 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 235 (accept_3_3 8 108 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 108 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 235 (accept_3_3 5 108
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 235
  (Polychromatic418967fa.accept_16_4_12_11_1_2650 4 108 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 108 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 108 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 235 (accept_3_3 2 108 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 108 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 108 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 235 (allA_of_3_1 107 107 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 235
  (allA_succ_of_accept 105 106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 106 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 235 (accept_3_3 104 106 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 106 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 103 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 102 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 106 235 (accept_3_3 101 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 106 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 100 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 106 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 235 (accept_3_3 98 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 96 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 235 (accept_3_3 95 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 94 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 235 (accept_3_3 92 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 91 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 235
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 90 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 106 235 (accept_3_3 89 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 106 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 106 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 235 (accept_3_3 86 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 84 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 235 (accept_3_3 83 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 235 (accept_3_3 80 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 79 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 235 (accept_3_3 77 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 235 (accept_3_3 74 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 235
  (Polychromatic418967fa.accept_19_15_11_7_1_8711 72 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 106 235 (accept_3_3 71 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 106 235 (Polychromatic418967fa.accept_19_13_11_7_1_4451 70 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 69
  106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 235 (accept_3_3 68
  106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 235
  (Polychromatic418967fa.accept_9_4_7_1_1_379 67 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 106 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 106 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 106 235 (accept_3_3 65 106 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 106 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 64 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 106 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63
  106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 235 (accept_3_3 62
  106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 106 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 106 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 106 235 (accept_3_3 59 106 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 106 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 235 (accept_3_3 56
  106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 235
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 55 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 106 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 106 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 106 235 (accept_3_3 53 106 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 106 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 106 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51
  106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 235 (accept_3_3 50
  106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 106 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 106 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 106 235 (accept_3_3 47 106 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 106 235 (Polychromatic418967fa.accept_14_4_8_11_1_794 46 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 106 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 106 235 (accept_3_3 44 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 106 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 43 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 106 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 106 235 (accept_3_3 41 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 106 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 106 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 106 235 (accept_3_3 38 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 106 235 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 106 235 (accept_3_3 35 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 106 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 106 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 106 235 (accept_3_3 32 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 106 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 106 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 106 235 (accept_3_3 29 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 106 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 106 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 106 235 (accept_3_3 26 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 106 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 106 235 (accept_3_3 23 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 106 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 106 235 (accept_3_3 20 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 106 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 106 235 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 106 235 (accept_3_3 17 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 106 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 106
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 106 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 106 235 (accept_3_3 14 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 106 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 106 235 (accept_3_3 11 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 106 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 106 235 (accept_3_3 8 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  106 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 106 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 106 235 (accept_3_3 5 106 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 106 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 106 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 106 235 (accept_3_3 2 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  106 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 106
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 235 (allA_succ_of_accept 104 105 235 (accept_3_3 104 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 103 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 105
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 235 (accept_3_3 101 105
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 105 235 5 20 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 105 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 99 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 105 235 (accept_3_3 98 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 105 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 97 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 105 235 (Polychromatic418967fa.accept_17_11_3_14_1_6736 96 105 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 105 235 5 19 21 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 105 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 94 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 235 (accept_3_3 92 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 105 235 (Polychromatic418967fa.accept_17_6_3_14_1_2078 91 105 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 105 235 5 18 21 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 105 235 (accept_3_3 89 105 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 88
  105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 105 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 87 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 105 235 (accept_3_3 86 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  105 235 5 17 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 105 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 84 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 235 (accept_3_3 83 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 105 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 105 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 105 235
  (Polychromatic418967fa.accept_19_5_10_7_1_5887 81 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 105 235 5 16 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 105 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 105 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 78
  105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 235 (accept_3_3 77
  105 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 76 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 235 5 15 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 235 (accept_3_3 74 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 235 (Polychromatic418967fa.accept_14_3_7_11_1_765 73 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 235 (Polychromatic418967fa.accept_20_12_5_15_1_14100 72
  105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 235 (accept_3_3 71
  105 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 235 5 14 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 105 235
  (Polychromatic418967fa.accept_16_5_9_11_1_3762 69 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 105 235 (accept_3_3 68 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 105 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 105 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 105 235 5 13 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 105 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 105 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 235 (accept_3_3 62 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 105 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 105 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 235 5 12 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 235 (accept_3_3 59 105 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 105 235 (accept_3_3 56 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  105 235 5 11 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 105 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 235 (accept_3_3 53 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 105 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 235 (Polychromatic418967fa.accept_12_3_9_7_1_472
  51 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 105 235 5 10 21 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 105 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 105 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 235 (accept_3_3 47 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 105 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 105 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 235 5 9 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 235 (accept_3_3 44 105 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 105 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 235 (accept_3_3 41 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  105 235 5 8 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 105 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 235 (accept_3_3 38 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 235 (Polychromatic418967fa.accept_16_5_9_11_1_3762 37 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 235 (Polychromatic418967fa.accept_16_4_9_11_1_7159 36 105
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 235 5 7 21 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 105 235 (Polychromatic418967fa.accept_19_14_10_7_1_8723 33 105 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 235 (accept_3_3 32 105 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 105 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 235 5 6 21 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 235 (accept_3_3 29 105 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 105 235 (accept_3_3 26 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  105 235 5 5 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 105 235 (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 235 (accept_3_3 23 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 105 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 105 235 5 4 21 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 235
  (Polychromatic418967fa.accept_17_2_3_14_1_8043 19 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 235 (accept_3_3 17 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 105 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 235 5 3 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 235 (accept_3_3 14 105 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 105 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 235 (accept_3_3 11 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  105 235 5 2 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 105 235 (Polychromatic418967fa.accept_19_9_10_7_1_10002 9 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 235 (accept_3_3 8 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 235 5 1 21 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 105 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 235 (accept_3_3 2 105 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 105 235 (Polychromatic418967fa.accept_19_1_10_7_1_14087 1 105 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 235 (allA_of_3_1 104 104 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 235
  (allA_succ_of_accept 102 103 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 102 103 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 235 (accept_3_3 101 103 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 100 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 99 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 235 (accept_3_3 98 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 97 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 96 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 235 (accept_3_3 95 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 94 103 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 93 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 235 (accept_3_3 92 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 91 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 235 (accept_3_3 89 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 87 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 235 (accept_3_3 86 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 235 (accept_3_3 83 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 235 (Polychromatic418967fa.accept_10_2_3_5_1_996 82 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 235
  (Polychromatic418967fa.accept_17_13_1_14_1_1149 81 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 103 235 (accept_3_3 80 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 103 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 103 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 103 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 103 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 235 (accept_3_3 77 103 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 235 (Polychromatic418967fa.accept_7_6_5_4_1_297
  76 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 75 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 235 (accept_3_3 74 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 235 (Polychromatic418967fa.accept_13_8_12_1_1_4662 73 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 235 (accept_3_3 71 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 235 (accept_3_3 68 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 67 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 235 (accept_3_3 65 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 235
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 63 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 103 235 (accept_3_3 62 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 103 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 103 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 103 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 235 (accept_3_3 59 103 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 235 (Polychromatic418967fa.accept_7_2_5_4_1_115
  58 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 235 (accept_3_3 56 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 235 (Polychromatic418967fa.accept_13_2_12_1_1_343 54 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 235 (accept_3_3 53 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 103 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 235 (accept_3_3 50 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 235 (accept_3_3 47 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 46 103 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 235
  (Polychromatic418967fa.accept_20_5_3_15_1_6909 45 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 235 (accept_3_3 44 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 235 (accept_3_3 41 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 235 (Polychromatic418967fa.accept_23_17_11_5_1_9195 40 103 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 235 (accept_3_3 38 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 235 (accept_3_3 35 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 235 (accept_3_3 32 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 235 (Polychromatic418967fa.accept_13_5_12_1_1_2123 31 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 235 (accept_3_3 29 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 235 (accept_3_3 26 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 235 (accept_3_3 23 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 235 (accept_3_3 20 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 235 (accept_3_3 17 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 103 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 235 (accept_3_3 14 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 235 (accept_3_3 11 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 235 (Polychromatic418967fa.accept_17_10_1_14_1_489 10 103 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 235 (accept_3_3 8 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 235 (accept_3_3 5 103 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 103 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 235 (accept_3_3 2 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 103 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 235 (allA_succ_of_accept 101 102 235 (accept_3_3 101 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 102 235 (Polychromatic418967fa.accept_13_9_11_1_1_1375 100 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 102 235
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 99 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 102 235 (accept_3_3 98 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 102 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 102 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 96 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 102 235 (accept_3_3 95 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 102 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 94 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 102 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 102 235 (accept_3_3 92 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 102 235 (Polychromatic418967fa.accept_14_7_4_11_1_3038 91 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 102 235 (Polychromatic418967fa.accept_13_12_11_1_1_2920 90 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 102 235 (accept_3_3 89 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 102 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 102 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 102 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 87 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 102 235 (accept_3_3 86 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 102 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 102 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 84 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 102 235 (accept_3_3 83 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 235 (Polychromatic418967fa.accept_15_7_12_10_1_4335 82 102
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 102 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 102 235 (accept_3_3 80 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 102 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 102 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 78 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 102 235 (accept_3_3 77 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 102 235
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 75 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 102 235 (accept_3_3 74 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 102 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 102 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 235 (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 102
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 102 235 (accept_3_3 71 102
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 235
  (Polychromatic418967fa.accept_9_7_3_1_1_386 70 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 102 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 102 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 235 (accept_3_3 68 102 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 102 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 235
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 66 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 102 235 (accept_3_3 65 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 102 235 (Polychromatic418967fa.accept_13_12_11_1_1_2920 64 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 102 235 (Polychromatic418967fa.accept_10_3_2_5_1_295
  63 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 235 (accept_3_3 62
  102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 102 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 102 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 102 235 (accept_3_3 59 102 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 102 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 102 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 235 (accept_3_3 56
  102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 235
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 55 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 102 235 (Polychromatic418967fa.accept_15_9_12_10_1_809 54 102 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 102 235 (accept_3_3 53 102 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 102 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 235 (Polychromatic418967fa.accept_9_6_3_1_1_155
  51 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 235 (accept_3_3 50
  102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 102 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 102 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 102 235 (accept_3_3 47 102 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 102 235 (Polychromatic418967fa.accept_13_7_11_1_1_2903 46 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 102 235 (accept_3_3 44 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 102 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 102 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 102 235 (accept_3_3 41 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 235
  (Polychromatic418967fa.accept_15_9_12_10_1_809 39 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 102 235 (accept_3_3 38 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 102 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 102 235 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 235 (accept_3_3 35 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 102 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 102 235 (accept_3_3 32 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 102 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 102 235 (Polychromatic418967fa.accept_20_10_2_15_1_1517 30 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 235 (accept_3_3 29 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 102
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 235
  (Polychromatic418967fa.accept_10_7_2_5_1_298 27 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 102 235 (accept_3_3 26 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 102 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 102 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 235 (accept_3_3 23 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 102 235 (accept_3_3 20 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 102 235 (Polychromatic418967fa.accept_16_3_6_11_1_2718 19 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 102 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 235 (accept_3_3 17 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 102 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 102 235 (accept_3_3 14 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 102 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 102 235 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 235 (accept_3_3 11 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 235 (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 102
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 102 235 (accept_3_3 8 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  102 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 102 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 235 (accept_3_3 5 102 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 102 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 235
  (Polychromatic418967fa.accept_10_3_2_5_1_295 3 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 102 235 (accept_3_3 2 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  102 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 102
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 235 (allA_of_3_1 101 101 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 235 (allA_succ_of_accept 99
  100 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 100 235 (accept_3_3 98 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 100 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 97 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 100 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 100 235 5 19 20 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 100 235
  (Polychromatic418967fa.accept_12_10_4_7_1_948 94 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 100 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 100 235 (accept_3_3 92 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 100 235 (Polychromatic418967fa.accept_17_6_15_14_1_8027 91 100 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 100 235 5 18 20 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 100 235 (accept_3_3 89 100 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 100 235
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 88 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 100 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 100 235 (accept_3_3 86 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 85 100 235 5 17 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 84 100 235 (Polychromatic418967fa.accept_13_6_9_1_1_5604 84 100 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 100 235 (accept_3_3 83 100 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 100 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 100 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 100 235 5 16 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 100 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 100 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 100 235
  (Polychromatic418967fa.accept_19_2_5_7_1_10021 78 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 100 235 (accept_3_3 77 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 100 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 100 235 5 15 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 100 235 (accept_3_3 74 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 100 235 (Polychromatic418967fa.accept_13_8_9_1_1_2147 73 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 100 235 (Polychromatic418967fa.accept_16_8_4_11_1_2687 72 100
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 100 235 (accept_3_3 71 100
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 100 235 5 14 20 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 100 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 100 235 (accept_3_3 68 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 100 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 67 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 100 235 (Polychromatic418967fa.accept_19_9_5_7_1_5853 66 100 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 100 235 5 13 20 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 100 235
  (Polychromatic418967fa.accept_28_8_16_11_1_14099 64 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 100 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 100 235 (accept_3_3 62 100 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 100 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 100 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 100 235 5 12 20 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 100 235 (accept_3_3 59 100 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 235 (Polychromatic418967fa.accept_12_10_4_7_1_948
  58 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 100 235 (accept_3_3 56 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  100 235 5 11 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 100 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 100 235 (accept_3_3 53 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 100 235 (Polychromatic418967fa.accept_11_8_1_4_1_2318 52 100 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 100 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 100 235 5 10 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 100 235 (Polychromatic418967fa.accept_13_10_9_1_1_5609 49 100 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 100 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 100 235 (accept_3_3 47 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 100 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 100 235 5 9 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 100 235 (accept_3_3 44 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 100 235 (Polychromatic418967fa.accept_23_20_8_5_1_14098 43 100 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 235
  (Polychromatic418967fa.accept_28_14_16_11_1_3967 42 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 100 235 (accept_3_3 41 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 235 5 8 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 100 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 100 235 (accept_3_3 38 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 100 235 (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 100 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 235
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 100 235 5 7 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 100 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 235 (accept_3_3 32 100 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 100 235 (Polychromatic418967fa.accept_8_7_4_3_1_156
  31 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 235 5 6 20 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 235
  (accept_3_3 29 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 235
  (Polychromatic418967fa.accept_13_2_9_1_1_67 28 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 100 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 235 (accept_3_3 26 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 100 235 5 5 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 100 235 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 100 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 235 (accept_3_3 23 100 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 100
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 235 5 4 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 100 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 235 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 100
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 235 (accept_3_3 17 100
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 235
  (Polychromatic418967fa.accept_17_16_15_14_1_6747 16 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 100 235 5 3 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 100 235 (accept_3_3 14 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 100 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 100 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 100 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 235 (accept_3_3 11 100 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 235 5 2 20 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 235 (accept_3_3 8 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 100 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 100 235 5 1 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 100 235 (Polychromatic418967fa.accept_23_4_8_5_1_7448 4
  100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 235 (accept_3_3 2 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 235 (Polychromatic418967fa.accept_22_1_12_15_1_6077 1 100 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  235 (allA_succ_of_accept 98 99 235 (accept_3_3 98 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 235 (Polychromatic418967fa.accept_13_6_8_1_1_2913 97 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 235 (accept_3_3 95 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 93 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 235 (accept_3_3 92 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 91 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 235 (Polychromatic418967fa.accept_13_12_8_1_1_825 90 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 235 (accept_3_3 89 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 87 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 235 (accept_3_3 86 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 235 (Polychromatic418967fa.accept_13_7_8_1_1_2145 85 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 235 (accept_3_3 83 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 235
  (Polychromatic418967fa.accept_10_1_9_5_1_83 81 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 235 (accept_3_3 80 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 235 (Polychromatic418967fa.accept_15_4_9_10_1_5384 79 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 235 (Polychromatic418967fa.accept_15_3_9_10_1_2325 78 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 235 (accept_3_3 77 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 99 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 235 (accept_3_3 74 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 235 (Polychromatic418967fa.accept_13_7_8_1_1_2145 72 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 235 (accept_3_3 71 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 69 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 235 (accept_3_3 68 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 235 (Polychromatic418967fa.accept_22_1_11_15_1_6075 67 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 235 (accept_3_3 65 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 235
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 63 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 235 (accept_3_3 62 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 235 (Polychromatic418967fa.accept_14_4_1_11_1_5026 60 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 235 (accept_3_3 59 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 99 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 235 (accept_3_3 56 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 235 (Polychromatic418967fa.accept_16_7_3_11_1_3682 55 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 235 (accept_3_3 53 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 235
  (Polychromatic418967fa.accept_10_1_9_5_1_83 51 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 235 (accept_3_3 50 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 235 (Polychromatic418967fa.accept_15_4_9_10_1_5384 49 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 235 (Polychromatic418967fa.accept_13_9_8_1_1_824 48 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 235 (accept_3_3 47 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 235 (accept_3_3 44 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 235 (Polychromatic418967fa.accept_22_21_11_15_1_14097 43 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 235 (Polychromatic418967fa.accept_15_12_9_10_1_2326 42 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 235 (accept_3_3 41 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 235
  (Polychromatic418967fa.accept_16_7_3_11_1_3682 39 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 235 (accept_3_3 38 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 235 (Polychromatic418967fa.accept_13_11_8_1_1_3815 37 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 235 (accept_3_3 35 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 235 (accept_3_3 32 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 235 (Polychromatic418967fa.accept_16_14_3_11_1_5969 30 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 235 (accept_3_3 29 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 235
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 235 (accept_3_3 26 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 235 (Polychromatic418967fa.accept_13_12_8_1_1_825 25 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 235 (accept_3_3 23 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 235
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 235 (accept_3_3 20 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 235 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 235 (accept_3_3 17 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 235
  (Polychromatic418967fa.accept_16_15_3_11_1_5997 15 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 235 (accept_3_3 14 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 235 (Polychromatic418967fa.accept_19_13_4_7_1_5878 13 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 235 (accept_3_3 11 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 235 (accept_3_3 8 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  235 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 235 (accept_3_3 5 99 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 235 (accept_3_3 2 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  235 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 99 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 98 235 (allA_of_3_1 98 98 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 235
  (allA_succ_of_accept 96 97 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 97 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 235 (accept_3_3 95 97 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 93
  97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 235 (accept_3_3 92 97
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 235
  (Polychromatic418967fa.accept_15_1_7_10_1_287 91 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 97 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 97 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 235 (accept_3_3 89 97 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 97 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 88 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 87
  97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 235 (accept_3_3 86 97
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 235
  (Polychromatic418967fa.accept_9_4_7_1_1_379 85 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 97 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 84 97 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 235 (accept_3_3 83 97 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 97 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 235 (Polychromatic418967fa.accept_13_3_6_1_1_3797
  81 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 235 (accept_3_3 80
  97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 79 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 97 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 97 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 235 (accept_3_3 77 97 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 97 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 75
  97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 235 (accept_3_3 74 97
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 235 (Polychromatic418967fa.accept_7_3_6_4_1_30
  73 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 235 (accept_3_3 71 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 235 (accept_3_3 68 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 235 (accept_3_3 65 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 235 (Polychromatic418967fa.accept_15_4_7_10_1_807 64 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 235 (accept_3_3 62 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 235 (accept_3_3 59 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 235 (accept_3_3 56 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 235 (Polychromatic418967fa.accept_13_3_6_1_1_3797 55 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 235 (accept_3_3 53 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 235 (accept_3_3 50 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 235 (accept_3_3 47 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 235 (accept_3_3 44 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 235 (accept_3_3 41 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 235 (accept_3_3 38 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 235
  (Polychromatic418967fa.accept_19_17_2_7_1_11422 36 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 235 (accept_3_3 35 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 235 (accept_3_3 32 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 235 (accept_3_3 29 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 235 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 235 (accept_3_3 26 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 235 (Polychromatic418967fa.accept_20_5_17_15_1_6858 25 97
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 235 (accept_3_3 23 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 235 (accept_3_3 20 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 235 (accept_3_3 17 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 235 (accept_3_3 14 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 235 (accept_3_3 11 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 235 (accept_3_3 8 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 235 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 97 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 235 (accept_3_3 5 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 97 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 97 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 235 (accept_3_3 2 97 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 97 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 235
  (allA_succ_of_accept 95 96 235 (accept_3_3 95 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  96 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 94 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 96 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 96 235 (accept_3_3 92 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 91 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 90 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 96 235 (accept_3_3 89 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  96 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 88 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 96 235 (Polychromatic418967fa.accept_13_9_5_1_1_1382 87 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 235 (accept_3_3 86 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 235 (accept_3_3 83 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  96 235 (Polychromatic418967fa.accept_13_4_5_1_1_833 82 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 81 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 235 (accept_3_3 80 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 78 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 96 235 (accept_3_3 77 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  96 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 96 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 235 (accept_3_3 74 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 73 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 72 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 235 (accept_3_3 71 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  96 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 235 (accept_3_3 68 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 235 (accept_3_3 65 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539 63 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 235 (accept_3_3 62 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 96 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 235
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 60 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 235 (accept_3_3 59 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 235 (accept_3_3 56 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 235
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 235 (accept_3_3 53 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 235 (accept_3_3 50 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 235 (accept_3_3 47 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 235 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 235 (accept_3_3 44 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 235
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 42 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 235 (accept_3_3 41 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 235 (accept_3_3 38 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 235 (accept_3_3 35 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 235 (accept_3_3 32 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 96 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 235 (accept_3_3 29 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 235 (Polychromatic418967fa.accept_21_7_12_4_1_6493 28 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 235 (accept_3_3 26 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 235
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 235 (accept_3_3 23 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 235 (accept_3_3 20 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 235
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 235 (accept_3_3 17 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 235 (accept_3_3 14 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 235 (accept_3_3 11 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 235 (Polychromatic418967fa.accept_19_10_1_7_1_10040 10 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 235 (accept_3_3 8 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 235 (accept_3_3 5 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  235 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 96 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 96 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 235 (accept_3_3 2 96 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 96 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 235
  (allA_of_3_1 95 95 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 235 (allA_succ_of_accept 93 94 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 94 235 (accept_3_3 92 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  94 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 91 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 94 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 235 (accept_3_3 89 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 94 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 94 235 (accept_3_3 86 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  94 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 94 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 235 (accept_3_3 83 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 235 (Polychromatic418967fa.accept_13_4_3_1_1_2898 82 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 235 (accept_3_3 80 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 235 (accept_3_3 77 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 235 (accept_3_3 74 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 235 (Polychromatic418967fa.accept_13_7_3_1_1_814 72 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 235 (accept_3_3 71 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 235 (accept_3_3 68 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 235 (Polychromatic418967fa.accept_13_2_3_1_1_3823 67 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 235 (accept_3_3 65 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 235 (accept_3_3 62 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 235 (accept_3_3 59 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 235 (Polychromatic418967fa.accept_13_6_3_1_1_1413 58 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 235 (accept_3_3 56 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 235 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 235 (accept_3_3 53 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 235 (accept_3_3 50 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 47 94 235 47 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 46 94 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 46
  94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 235 (accept_3_3 44 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 235 (accept_3_3 41 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 235 (accept_3_3 38 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 235 (accept_3_3 35 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 235 (accept_3_3 32 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 235 (accept_3_3 29 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 235 (accept_3_3 26 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 235 (accept_3_3 23 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 235 (accept_3_3 20 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 235 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 235 (accept_3_3 17 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 94 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 235 (accept_3_3 14 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 235 (accept_3_3 11 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 235 (Polychromatic418967fa.accept_19_10_18_7_1_12729 10 94 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 235 (accept_3_3 8 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 94 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 94 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 235 (accept_3_3 5 94 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 94 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 235 (accept_3_3 2 94 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 235
  (allA_succ_of_accept 92 93 235 (accept_3_3 92 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 235 (Polychromatic418967fa.accept_17_6_8_14_1_6706 91 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 235 (accept_3_3 89 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 87 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 235 (accept_3_3 86 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 85 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 235 (Polychromatic418967fa.accept_13_6_2_1_1_2137 84 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 235 (accept_3_3 83 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 235
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 81 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 235 (accept_3_3 80 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 235 (accept_3_3 77 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 235 (accept_3_3 74 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 235 (Polychromatic418967fa.accept_15_13_3_10_1_2296 73 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 235 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 235 (accept_3_3 71 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 235 (accept_3_3 68 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 235 (accept_3_3 65 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 235 (accept_3_3 62 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 235 (accept_3_3 59 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 235
  (Polychromatic418967fa.accept_10_7_3_5_1_301 57 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 235 (accept_3_3 56 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 235 (accept_3_3 53 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 235 (accept_3_3 50 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 235 (accept_3_3 47 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 235
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 235 (accept_3_3 44 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 235 (accept_3_3 41 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 235 (accept_3_3 38 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 235 (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 235 (accept_3_3 35 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 235 (accept_3_3 32 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 235 (accept_3_3 29 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 235 (accept_3_3 26 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 235 (accept_3_3 23 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 235
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 235 (accept_3_3 20 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 235 (accept_3_3 17 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 235 (accept_3_3 14 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 235 (accept_3_3 11 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 235
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 235 (accept_3_3 8 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 235 (accept_3_3 5 93 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 3
  93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 235 (accept_3_3 2 93 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 235 (Polychromatic418967fa.accept_22_1_5_15_1_3074
  1 93 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 235
  (allA_of_3_1 92 92 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 235 (allA_succ_of_accept 90 91 235
  (Polychromatic418967fa.accept_19_14_15_7_1_7205 90 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 235 (accept_3_3 89 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 235 (Polychromatic418967fa.accept_14_4_7_11_1_790 88 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 235 (Polychromatic418967fa.accept_14_3_7_11_1_765 87 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 235 (accept_3_3 86 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 235 (Polychromatic418967fa.accept_20_5_11_15_1_3920 85 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 235
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 84 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 91 235 (accept_3_3 83 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 82 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 235 (Polychromatic418967fa.accept_15_6_1_10_1_1549 81 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 235 (accept_3_3 80 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 79 91 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 235
  (Polychromatic418967fa.accept_22_12_3_15_1_7889 78 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 91 235 (accept_3_3 77 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 235 (Polychromatic418967fa.accept_10_6_1_5_1_1024 76 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 235 (Polychromatic418967fa.accept_17_7_6_14_1_6737 75 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 235 (accept_3_3 74 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 73 91 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 235
  (Polychromatic418967fa.accept_25_22_16_10_1_12394 72 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 91 235 (accept_3_3 71 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 91 235 (Polychromatic418967fa.accept_19_13_15_7_1_5843 70 91 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 69 91 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 235 (accept_3_3 68 91 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 235 (Polychromatic418967fa.accept_15_7_1_10_1_305
  67 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 235
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 66 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 235 (accept_3_3 65 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 64 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 235 (Polychromatic418967fa.accept_22_19_3_15_1_14096 63 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 235 (accept_3_3 62 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 235 (Polychromatic418967fa.accept_21_19_7_4_1_4994 61 91
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 235
  (Polychromatic418967fa.accept_14_4_7_11_1_790 60 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 235 (accept_3_3 59 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 58 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 235 (Polychromatic418967fa.accept_25_7_16_10_1_12358 57 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 235 (accept_3_3 56 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 235 (Polychromatic418967fa.accept_19_17_15_7_1_10030 55 91
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 235
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 235 (accept_3_3 53 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 235 (Polychromatic418967fa.accept_14_10_7_11_1_3015 52 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 235 (accept_3_3 50 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 235
  (Polychromatic418967fa.accept_21_6_7_4_1_4993 48 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 235 (accept_3_3 47 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 235 (Polychromatic418967fa.accept_10_6_1_5_1_1024 46 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 235 (Polychromatic418967fa.accept_14_3_7_11_1_765 45 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 235 (accept_3_3 44 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 43 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 235
  (Polychromatic418967fa.accept_17_8_6_14_1_6718 42 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 235 (accept_3_3 41 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 40 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 235 (accept_3_3 38 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 235
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 235 (accept_3_3 35 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 34 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 235 (Polychromatic418967fa.accept_19_14_15_7_1_7205 33 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 235 (accept_3_3 32 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 235 (Polychromatic418967fa.accept_14_3_7_11_1_765 31 91 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 235
  (Polychromatic418967fa.accept_19_11_15_7_1_3177 30 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 235 (accept_3_3 29 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 235 (Polychromatic418967fa.accept_19_8_15_7_1_323 27 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 235 (accept_3_3 26 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 235 (Polychromatic418967fa.accept_17_8_6_14_1_6718 25 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 235
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 235 (accept_3_3 23 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 22 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 235 (Polychromatic418967fa.accept_15_6_1_10_1_1549 21 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 235 (accept_3_3 20 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 91 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 235
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 235 (accept_3_3 17 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 235 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 235 (Polychromatic418967fa.accept_17_15_6_14_1_4239 15 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 235 (accept_3_3 14 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 91
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 235
  (Polychromatic418967fa.accept_19_12_15_7_1_11432 12 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 91 235 (accept_3_3 11 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 91 235 (Polychromatic418967fa.accept_14_10_7_11_1_3015 10 91 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 91 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 235 (accept_3_3 8 91 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 7
  91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 235
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 235 (accept_3_3 5 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 91 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 235 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 235 (accept_3_3 2 91 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 235 (Polychromatic418967fa.accept_21_1_7_4_1_4947 1 91 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 235
  (allA_succ_of_accept 89 90 235 (accept_3_3 89 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  90 235 (Polychromatic418967fa.accept_19_12_14_7_1_5865 88 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 90 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 235 (accept_3_3 86 90 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 85 90 235 5 17 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 90 235 (Polychromatic418967fa.accept_19_8_14_7_1_10047 84 90
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 90 235 (accept_3_3 83 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 82
  90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 90 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 235 5 16 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 90 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 235 (Polychromatic418967fa.accept_17_10_5_14_1_4203 78 90
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 235 (accept_3_3 77 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 90 235
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 76 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 90 235 5 15 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 90 235 (accept_3_3 74 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  90 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 90 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 90 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 235 (accept_3_3 71 90 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 235 5 14 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 235 (accept_3_3 68 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 235 (Polychromatic418967fa.accept_13_2_12_1_1_343
  67 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 90 235 5 13 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 90 235 (Polychromatic418967fa.accept_11_9_2_4_1_707 64 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 90 235 (Polychromatic418967fa.accept_13_11_12_1_1_2154 63 90
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 235 (accept_3_3 62 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 235 5 12 18 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 235 (accept_3_3 59
  90 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 58 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 90 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 235 (accept_3_3 56 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 90 235 5 11 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 90 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 90 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 235 (accept_3_3 53 90 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 235 5 10 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 235 (Polychromatic418967fa.accept_19_10_14_7_1_11440 48 90
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 235 (accept_3_3 47 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 235
  (Polychromatic418967fa.accept_19_8_14_7_1_10047 46 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 235 5 9 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 235 (accept_3_3 44 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  90 235 (Polychromatic418967fa.accept_17_9_5_14_1_4277 43 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 90 235 (Polychromatic418967fa.accept_11_9_2_4_1_707 42 90 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 235 (accept_3_3 41 90 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 235 5 8 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 90 235 (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 90 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 235 (accept_3_3 38 90 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 235
  (Polychromatic418967fa.accept_17_2_5_14_1_2068 36 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 90 235 5 7 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 90 235 (Polychromatic418967fa.accept_13_8_12_1_1_4662 34 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 235 (accept_3_3 32 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 235 5 6 18 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 235 (accept_3_3 29
  90 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 235
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 90 235 (Polychromatic418967fa.accept_17_10_5_14_1_4203 27 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 235 (accept_3_3 26 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 90 235 5 5 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 90 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 90 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 235 (accept_3_3 23 90 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 235 (Polychromatic418967fa.accept_19_3_14_7_1_7204 22 90 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 235 5 4 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 235 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 90
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 235 (accept_3_3 17 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16
  90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 235 5 3 18 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 235 (accept_3_3 14
  90 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 90 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 235 (accept_3_3 11 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 235 5 2 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 235 (accept_3_3 8 90 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 235 (Polychromatic418967fa.accept_20_7_10_15_1_14095 7 90 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 235
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 90 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 90 235 5 1 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 90 235 (Polychromatic418967fa.accept_19_4_14_7_1_5863 4 90 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 235 (accept_3_3 2 90 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 235
  (allA_of_3_1 89 89 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 235 (allA_succ_of_accept 87 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 88 235 (accept_3_3 86 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  88 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 88 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 84 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 235 (accept_3_3 83 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 82 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 88 235 (accept_3_3 80 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  88 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 79 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 88 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 78 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 235 (accept_3_3 77 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 235 (accept_3_3 74 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 73 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 235 (accept_3_3 71 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 235 (accept_3_3 68 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 88 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 235 (accept_3_3 65 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 235 (Polychromatic418967fa.accept_14_8_4_11_1_3035 64 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 88 235 (accept_3_3 62 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  88 235 (Polychromatic418967fa.accept_13_9_10_1_1_1389 61 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 88 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 235 (accept_3_3 59 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 235 (accept_3_3 56 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 235 (Polychromatic418967fa.accept_23_9_19_5_1_4082 55 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 235 (Polychromatic418967fa.accept_19_16_12_7_1_8712 54 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 235 (accept_3_3 53 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 52 88 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 235 (accept_3_3 50 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 235 (accept_3_3 47 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 235 (accept_3_3 44 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 43 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 235 (accept_3_3 41 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 235 (accept_3_3 38 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 235 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 235 (accept_3_3 35 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 88 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 235 (accept_3_3 32 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 235 (accept_3_3 29 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 235 (Polychromatic418967fa.accept_16_12_8_11_1_2695 28 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 235 (accept_3_3 26 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 235 (Polychromatic418967fa.accept_18_7_16_1_1_4951 25 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 235 (accept_3_3 23 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 235 (accept_3_3 20 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 235 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 235 (accept_3_3 17 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 88
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 235 (accept_3_3 14 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 235 (accept_3_3 11 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 235 (accept_3_3 8 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 88 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 235 (accept_3_3 5 88 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 88 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 88 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 88 235 (accept_3_3 2 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88
  235 (Polychromatic418967fa.accept_14_1_4_11_1_3036 1 88 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 88 235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 87 235 (allA_succ_of_accept 86 87 235 (accept_3_3 86 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 87 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 87 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 87 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 87 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 235 (accept_3_3 83 87 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 82
  87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 235 (accept_3_3 80 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 235 (accept_3_3 77 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 75 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 235 (accept_3_3 74 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 73 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 235 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 235 (accept_3_3 71 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 235 (accept_3_3 68 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 235 (accept_3_3 65 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 235
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 235 (accept_3_3 62 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 235 (accept_3_3 59 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 235 (accept_3_3 56 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 54 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 235 (accept_3_3 53 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 235
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 51 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 235 (accept_3_3 50 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 235 (accept_3_3 47 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 235 (accept_3_3 44 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 235 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 235 (accept_3_3 41 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 235 (accept_3_3 38 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 235 (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 235 (accept_3_3 35 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 235
  (Polychromatic418967fa.accept_10_3_7_5_1_288 33 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 235 (accept_3_3 32 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 235 (accept_3_3 29 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 235 (accept_3_3 26 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 235 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 235 (accept_3_3 23 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 87 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 235 (accept_3_3 20 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 235 (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 235 (accept_3_3 17 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 235 (accept_3_3 14 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 235 (accept_3_3 11 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 87 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 235 (accept_3_3 8 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 235 (accept_3_3 5 87 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 235 (accept_3_3 2 87 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  87 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 235
  (allA_of_3_1 86 86 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 235 (allA_succ_of_accept 84 85 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 235 (accept_3_3 83 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 235 (Polychromatic418967fa.accept_13_3_7_1_1_334 81 85 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 85 235 5 16 17 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 85 235
  (Polychromatic418967fa.accept_9_7_4_1_1_391 79 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 235 (accept_3_3 77 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 235 (Polychromatic418967fa.accept_13_11_7_1_1_1386 76 85 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 85 235 5 15 17 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 85 235 (accept_3_3 74 85 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 73
  85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 235
  (Polychromatic418967fa.accept_16_8_5_11_1_4776 72 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 235 (accept_3_3 71 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 85
  235 5 14 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  85 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 85 235 (accept_3_3 68 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 85 235 (Polychromatic418967fa.accept_11_1_8_4_1_717 67 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 85 235 5 13 17 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 85 235
  (Polychromatic418967fa.accept_18_10_13_1_1_7736 64 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 85 235 (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 235 (accept_3_3 62 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 85 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 85 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 85 235 5 12 17 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 85 235 (accept_3_3 59 85 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 235 (accept_3_3 56 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 85
  235 5 11 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  85 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 85 235 (accept_3_3 53 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 85 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 85 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 85 235 5 10 17 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 85 235
  (Polychromatic418967fa.accept_19_11_9_7_1_4447 49 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 85 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 235 (accept_3_3 47 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 85 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 235 5 9 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 235 (accept_3_3 44 85 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 85 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 235 (accept_3_3 41 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 85
  235 5 8 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  85 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 85 235 (accept_3_3 38 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 85 235 (Polychromatic418967fa.accept_13_11_7_1_1_1386 37 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 235 (Polychromatic418967fa.accept_19_17_9_7_1_3171 36 85
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 85 235 5 7 17 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 85 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 85 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 235 (accept_3_3 32 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 85 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 85 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 85 235 5 6 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 235 (accept_3_3 29 85 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 235 (Polychromatic418967fa.accept_18_10_13_1_1_7736 28 85 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 235
  (Polychromatic418967fa.accept_19_8_9_7_1_312 27 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 235 (accept_3_3 26 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85
  235 5 5 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  85 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 85 235 (accept_3_3 23 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 85 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 85 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 85 235 5 4 17 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 85 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 85 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 235 (accept_3_3 17 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 85 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 235 5 3 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 235 (accept_3_3 14 85 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 235 (Polychromatic418967fa.accept_19_13_9_7_1_2038 13 85 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 235 (accept_3_3 11 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85
  235 5 2 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  85 235 (Polychromatic418967fa.accept_16_9_5_11_1_3776 9 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 85 235 (accept_3_3 8 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 85 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 85 235 5 1 17 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 85 235
  (Polychromatic418967fa.accept_14_4_1_11_1_5026 4 85 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 235 (accept_3_3 2 85 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 235 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 85 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 235
  (allA_succ_of_accept 83 84 235 (accept_3_3 83 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 235 (Polychromatic418967fa.accept_19_6_8_7_1_10023 82 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 81 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 235 (accept_3_3 80 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 84 235 (accept_3_3 77 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  84 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 84 235 (Polychromatic418967fa.accept_18_3_12_1_1_3787 75 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 235 (accept_3_3 74 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 235 (Polychromatic418967fa.accept_13_8_6_1_1_3808 73 84 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 235
  (Polychromatic418967fa.accept_13_7_6_1_1_368 72 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 235 (accept_3_3 71 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 235 (accept_3_3 68 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 235
  (Polychromatic418967fa.accept_10_6_4_5_1_615 66 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 84 235 (accept_3_3 65 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  84 235 (Polychromatic418967fa.accept_15_4_9_10_1_5384 64 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 235 (accept_3_3 62 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 235 (accept_3_3 59 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 235 (Polychromatic418967fa.accept_13_5_6_1_1_822 57 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 235 (accept_3_3 56 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 235
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 235 (accept_3_3 53 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  84 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 235 (accept_3_3 50 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 235
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 48 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 235 (accept_3_3 47 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 235 (Polychromatic418967fa.accept_17_11_16_14_1_6760 45 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 235 (accept_3_3 44 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 84 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 235 (accept_3_3 41 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 235 (accept_3_3 38 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 235 (Polychromatic418967fa.accept_19_18_8_7_1_4446 37 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 235
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 235 (accept_3_3 35 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 235 (accept_3_3 32 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 235
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 235 (accept_3_3 29 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 235 (Polychromatic418967fa.accept_13_2_6_1_1_3807 28 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 235 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 235 (accept_3_3 26 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 84 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 235 (accept_3_3 23 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 235 (accept_3_3 20 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 235
  (Polychromatic418967fa.accept_13_5_6_1_1_822 18 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 235 (accept_3_3 17 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 235 (accept_3_3 14 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 235
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 235 (accept_3_3 11 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 235 (Polychromatic418967fa.accept_20_10_4_15_1_12657 10 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 235 (accept_3_3 8 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 84 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 235 (accept_3_3 5 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 84 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 235 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 84 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 235 (accept_3_3 2 84 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 84 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 235 (allA_of_3_1
  83 83 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 235 (allA_succ_of_accept 81 82 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 235 (accept_3_3 80 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 235 (accept_3_3 77 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 235 (accept_3_3 74 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 235 (accept_3_3 71 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 235 (Polychromatic418967fa.accept_13_5_4_1_1_364 70 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 235 (accept_3_3 68 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 67 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 235 (Polychromatic418967fa.accept_23_20_13_5_1_14094 66 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 235 (accept_3_3 65 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 82 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 235 (accept_3_3 62 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 235 (Polychromatic418967fa.accept_19_3_6_7_1_10044 60 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 235 (accept_3_3 59 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 82 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 235 (accept_3_3 56 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 235 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 235 (accept_3_3 53 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 235 (accept_3_3 50 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 235 (accept_3_3 47 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 46 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 235 (accept_3_3 44 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 235 (Polychromatic418967fa.accept_13_3_4_1_1_363 42 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 235 (accept_3_3 41 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 235 (accept_3_3 38 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 235 (accept_3_3 35 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 235 (accept_3_3 32 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 235 (Polychromatic418967fa.accept_13_5_4_1_1_364 31 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 235 (accept_3_3 29 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 235 (accept_3_3 26 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 235 (Polychromatic418967fa.accept_19_5_6_7_1_10003 24 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 235 (accept_3_3 23 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 82 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 235 (accept_3_3 20 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 235 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 235 (accept_3_3 17 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 235 (accept_3_3 14 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 235 (Polychromatic418967fa.accept_15_12_7_10_1_3297 12 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 235 (accept_3_3 11 82 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 235 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 82 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 235 (accept_3_3 8 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  235 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 82 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 82 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 235 (accept_3_3 5 82 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 82 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 235 (accept_3_3 2 82 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 235
  (allA_succ_of_accept 80 81 235 (accept_3_3 80 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 79 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 235 (accept_3_3 77 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 75 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 235 (accept_3_3 74 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 235 (Polychromatic418967fa.accept_24_1_9_19_1_12488 73 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 235 (Polychromatic418967fa.accept_13_7_3_1_1_814 72 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 235 (accept_3_3 71 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 235
  (Polychromatic418967fa.accept_10_9_1_5_1_594 69 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 235 (accept_3_3 68 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 235 (Polychromatic418967fa.accept_13_2_3_1_1_3823 67 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 235 (accept_3_3 65 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 235 (accept_3_3 62 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 61 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 235 (Polychromatic418967fa.accept_16_12_1_11_1_5958 60 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 235 (accept_3_3 59 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 235
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 57 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 235 (accept_3_3 56 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 235 (Polychromatic418967fa.accept_17_4_13_14_1_1139 55 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 235 (accept_3_3 53 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 235 (accept_3_3 50 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539 48 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 235 (accept_3_3 47 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 235
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 235 (accept_3_3 44 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 235 (Polychromatic418967fa.accept_13_4_3_1_1_2898 43 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 235 (accept_3_3 41 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 235
  (Polychromatic418967fa.accept_10_9_1_5_1_594 39 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 235 (accept_3_3 38 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 235 (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 235 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 235 (accept_3_3 35 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 235
  (Polychromatic418967fa.accept_13_7_3_1_1_814 33 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 235 (accept_3_3 32 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 235 (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 235 (accept_3_3 29 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 235 (accept_3_3 26 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 235 (Polychromatic418967fa.accept_19_6_5_7_1_8708 25 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 235 (accept_3_3 23 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 235
  (Polychromatic418967fa.accept_17_4_13_14_1_1139 21 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 235 (accept_3_3 20 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 235 (accept_3_3 17 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 235 (accept_3_3 14 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 235 (Polychromatic418967fa.accept_19_13_5_7_1_12705 13 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 235 (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 235 (accept_3_3 11 81 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 235
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 235 (accept_3_3 8 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  235 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 235 (accept_3_3 5 81 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 3
  81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 235 (accept_3_3 2 81 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 1
  81 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 235 (allA_of_3_1 80
  80 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 235 (allA_succ_of_accept 78 79 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 235 (accept_3_3 77 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 235 (accept_3_3 74 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 73 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 235
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 72 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 235 (accept_3_3 71 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 235 (Polychromatic418967fa.accept_18_16_7_1_1_6332 70 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 235 (accept_3_3 68 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 235 (accept_3_3 65 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 64 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 235 (Polychromatic418967fa.accept_17_12_11_14_1_3120 63 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 235 (accept_3_3 62 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 79 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 60 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 235 (accept_3_3 59 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 235 (accept_3_3 56 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 235 (accept_3_3 53 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 235 (accept_3_3 50 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 235 (accept_3_3 47 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 46 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 235 (Polychromatic418967fa.accept_20_5_19_15_1_3946 45 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 235 (accept_3_3 44 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 79
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 235 (accept_3_3 41 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 235 (accept_3_3 38 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 235 (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 235 (accept_3_3 35 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 235 (accept_3_3 32 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 235 (accept_3_3 29 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 235 (accept_3_3 26 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 235 (Polychromatic418967fa.accept_17_8_11_14_1_6770 25 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 235 (accept_3_3 23 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 235 (accept_3_3 20 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 235
  (Polychromatic418967fa.accept_23_18_10_5_1_14093 18 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 79 235 (accept_3_3 17 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 79 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 79 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 79 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 235 (accept_3_3 14 79 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13
  79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 235 (accept_3_3 11 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 235 (Polychromatic418967fa.accept_16_10_15_11_1_3785 10 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 235 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 235 (accept_3_3 8 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 235 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 79 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 235 (accept_3_3 5 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  235 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 79 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 79 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 235 (accept_3_3 2 79 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 79 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 235
  (allA_succ_of_accept 77 78 235 (accept_3_3 77 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 235 (accept_3_3 74 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 235
  (Polychromatic418967fa.accept_10_2_8_5_1_587 72 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 235 (accept_3_3 71 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 235 (accept_3_3 68 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 235 (accept_3_3 65 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 235 (Polychromatic418967fa.accept_17_13_10_14_1_4211 64 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 235 (accept_3_3 62 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 235
  (Polychromatic418967fa.accept_14_4_8_11_1_794 60 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 235 (accept_3_3 59 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 235 (accept_3_3 56 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 235 (Polychromatic418967fa.accept_19_17_2_7_1_11422 55 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 235 (accept_3_3 53 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 235 (Polychromatic418967fa.accept_15_6_3_10_1_2341 51 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 235 (accept_3_3 50 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 235 (accept_3_3 47 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 235 (Polychromatic418967fa.accept_14_4_8_11_1_794 46 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 235 (accept_3_3 44 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 235
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 235 (accept_3_3 41 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 235 (accept_3_3 38 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 235
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 235 (accept_3_3 35 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 235 (accept_3_3 32 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 235 (accept_3_3 29 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 235 (Polychromatic418967fa.accept_15_13_3_10_1_2296 28 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 235 (accept_3_3 26 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 235 (accept_3_3 23 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 235 (accept_3_3 20 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 235
  (Polychromatic418967fa.accept_14_4_8_11_1_794 18 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 235 (accept_3_3 17 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 235 (Polychromatic418967fa.accept_27_15_24_19_1_10416 15 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 235 (accept_3_3 14 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 235 (accept_3_3 11 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 235 (accept_3_3 8 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 78 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 235
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 6 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 235 (accept_3_3 5 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  235 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 78 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 78 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 235 (accept_3_3 2 78 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 235 (allA_of_3_1 77 77
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 235 (allA_succ_of_accept 75 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 235 (accept_3_3 74 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 235 (accept_3_3 71 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 235 (accept_3_3 68 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 67 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 235 (accept_3_3 65 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 64 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 235 (accept_3_3 62 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 235 (accept_3_3 59 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 235 (accept_3_3 56 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 235 (accept_3_3 53 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 235 (accept_3_3 50 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 49 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 235 (accept_3_3 47 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 235 (accept_3_3 44 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 235 (accept_3_3 41 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 235 (accept_3_3 38 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 235 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 235 (accept_3_3 35 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 76 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 235 (accept_3_3 32 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 235 (accept_3_3 29 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 235 (accept_3_3 26 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 235 (accept_3_3 23 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 235 (accept_3_3 20 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 235 (Polychromatic418967fa.accept_20_18_16_15_1_3958 18 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 235 (accept_3_3 17 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 76 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 235 (accept_3_3 14 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 235 (accept_3_3 11 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 76 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 235 (accept_3_3 8 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 76 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 235 (accept_3_3 5 76 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 76 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 235 (accept_3_3 2 76 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 1
  76 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 235 (allA_succ_of_accept
  74 75 235 (accept_3_3 74 75 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 235
  (Polychromatic418967fa.accept_22_7_9_15_1_14086 73 75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 235 (accept_3_3 71 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 75 235 5 14 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 75 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 75 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 235 (accept_3_3 68 75 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 75 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 235
  (Polychromatic418967fa.accept_18_12_3_1_1_3685 66 75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 75 235 5 13 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 75 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 235 (Polychromatic418967fa.accept_13_11_10_1_1_1409 63 75
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 235 (accept_3_3 62 75 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 61
  75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 235 5 12 15 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 235 (accept_3_3 59
  75 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 58 75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 235 (accept_3_3 56 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 75 235 5 11 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 75 235 (Polychromatic418967fa.accept_29_25_17_3_1_14092 54 75 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 235 (accept_3_3 53 75 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 75 235 5 10 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 75 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 235 (accept_3_3 47 75 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 235 5 9 15 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 235 (accept_3_3 44
  75 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 235 (accept_3_3 41 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 75 235 5 8 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 75 235 (Polychromatic418967fa.accept_19_1_18_7_1_12744 39 75 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 235 (accept_3_3 38 75 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 75 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 75 235 5 7 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 75 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 235 (accept_3_3 32 75 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 31
  75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 235 5 6 15 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 235 (accept_3_3 29
  75 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 235 (accept_3_3 26 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 75 235 5 5 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 75 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 75 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 235 (accept_3_3 23 75 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 75 235 5 4 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 75 235 (Polychromatic418967fa.accept_21_19_12_4_1_8134 19 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 235 (Polychromatic418967fa.accept_21_18_12_4_1_4967 18 75
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 235 (accept_3_3 17 75 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 235 5 3 15 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 235 (accept_3_3 14
  75 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 235 (Polychromatic418967fa.accept_18_12_3_1_1_3685 12 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 235 (accept_3_3 11 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 75 235 5 2 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 75 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 235 (accept_3_3 8 75 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 75 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 75 235 5 1 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 75 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 235 (Polychromatic418967fa.accept_21_3_12_4_1_8116 3 75 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 235 (accept_3_3 2 75 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1
  75 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 235 (allA_of_3_1 74 74
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 235 (allA_succ_of_accept 72 73 235
  (Polychromatic418967fa.accept_10_2_3_5_1_996 72 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 235 (accept_3_3 71 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 235 (accept_3_3 68 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 67 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 235 (accept_3_3 65 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 235 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 235 (accept_3_3 62 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 235 (Polychromatic418967fa.accept_13_9_8_1_1_824 61 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 235
  (Polychromatic418967fa.accept_17_9_5_14_1_4277 60 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 235 (accept_3_3 59 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 235 (accept_3_3 56 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 235 (accept_3_3 53 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 235 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 235 (Polychromatic418967fa.accept_13_12_8_1_1_825 51 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 235 (accept_3_3 50 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 235 (Polychromatic418967fa.accept_14_7_3_11_1_2199 49 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 235 (accept_3_3 47 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 235 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 235 (accept_3_3 44 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 235 (accept_3_3 41 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 235 (Polychromatic418967fa.accept_19_2_16_7_1_11424 40 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 235 (Polychromatic418967fa.accept_25_14_23_10_1_1765 39 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 235 (accept_3_3 38 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 73 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 235 (accept_3_3 35 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 235 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 235 (accept_3_3 32 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 235 (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 235 (accept_3_3 29 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 235 (accept_3_3 26 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 235 (Polychromatic418967fa.accept_11_3_7_4_1_1133 25 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 235
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 235 (accept_3_3 23 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 235 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 235 (accept_3_3 20 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 235 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 73 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 235 (accept_3_3 17 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 235 (accept_3_3 14 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 235
  (Polychromatic418967fa.accept_10_2_3_5_1_996 12 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 235 (accept_3_3 11 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 235 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 235 (accept_3_3 8 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 235 (accept_3_3 5 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 73 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 235 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 235 (accept_3_3 2 73 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 235 (allA_succ_of_accept 71
  72 235 (accept_3_3 71 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 235
  (Polychromatic418967fa.accept_19_13_15_7_1_5843 70 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 72 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 235 (accept_3_3 68 72 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 67 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 235
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 66 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 72 235 (accept_3_3 65 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  72 235 (Polychromatic418967fa.accept_17_13_4_14_1_4272 64 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 72 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 235 (accept_3_3 62 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 235
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 60 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 235 (accept_3_3 59 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  72 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 57 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 235 (accept_3_3 56 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 72 235 (accept_3_3 53 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  72 235 (Polychromatic418967fa.accept_15_7_12_10_1_4335 52 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 235 (Polychromatic418967fa.accept_14_9_2_11_1_780 51 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 235 (accept_3_3 50 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 235 (Polychromatic418967fa.accept_19_11_15_7_1_3177 49 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 235 (accept_3_3 47 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 235 (Polychromatic418967fa.accept_11_2_6_4_1_3028 46 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 235 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 235 (accept_3_3 44 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 43 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 235
  (Polychromatic418967fa.accept_13_3_7_1_1_334 42 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 235 (accept_3_3 41 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 235 (Polychromatic418967fa.accept_15_9_12_10_1_809 39 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 235 (accept_3_3 38 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 72 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 235
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 235 (accept_3_3 35 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 235 (accept_3_3 32 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 235 (Polychromatic418967fa.accept_19_12_15_7_1_11432 31 72 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 235
  (Polychromatic418967fa.accept_17_13_4_14_1_4272 30 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 235 (accept_3_3 29 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 235 (accept_3_3 26 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 235 (Polychromatic418967fa.accept_20_5_12_15_1_9860 25 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 235
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 235 (accept_3_3 23 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 235 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 235 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 235 (accept_3_3 20 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 235
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 235 (accept_3_3 17 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 235 (Polychromatic418967fa.accept_13_3_7_1_1_334 16 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 235 (Polychromatic418967fa.accept_21_15_9_4_1_2207 15 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 235 (accept_3_3 14 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 235 (accept_3_3 11 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 235 (Polychromatic418967fa.accept_20_10_12_15_1_3940 10 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 235 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 235 (accept_3_3 8 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 235 (accept_3_3 5 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  235 (Polychromatic418967fa.accept_16_4_8_11_1_5961 4 72 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 235 (accept_3_3 2 72 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 235 (Polychromatic418967fa.accept_17_1_4_14_1_8058 1 72 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 235 (allA_of_3_1 71 71 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 235 (allA_succ_of_accept 69 70 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 235 (accept_3_3 68 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 70 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 70 235 5 13 14 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 70 235
  (Polychromatic418967fa.accept_12_4_10_7_1_149 64 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 70 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 70 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 235 (accept_3_3 62 70 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 70 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 235 5 12 14 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 235 (accept_3_3 59 70 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 70 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 235 (accept_3_3 56 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 70
  235 5 11 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  70 235 (Polychromatic418967fa.accept_17_3_2_14_1_6714 54 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 70 235 (accept_3_3 53 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 70 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 70 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 70 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 235 5 10 14 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 70 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 70 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 235 (accept_3_3 47 70 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 70 235 (Polychromatic418967fa.accept_18_10_16_1_1_1534 46 70 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 70 235 5 9 14 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 70 235 (accept_3_3 44 70 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 235 (Polychromatic418967fa.accept_13_4_5_1_1_833 43 70 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 235 (accept_3_3 41 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  235 5 8 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 70 235 (accept_3_3 38 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 70 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 235 (Polychromatic418967fa.accept_16_4_6_11_1_3753 36 70
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 70 235 5 7 14 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 70 235
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 34 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 70 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 235 (accept_3_3 32 70 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 70 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 70 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 235 5 6 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 235 (accept_3_3 29 70 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 70 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 235 (accept_3_3 26 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 70
  235 5 5 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  70 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 70 235 (accept_3_3 23 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 70 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 70 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 235 5 4 14 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 235
  (Polychromatic418967fa.accept_13_6_5_1_1_834 19 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 70 235 (Polychromatic418967fa.accept_16_2_6_11_1_1722 18 70 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 235 (accept_3_3 17 70 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 70 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 70 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 70 235 5 3 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 70 235 (accept_3_3 14 70 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 235 (accept_3_3 11 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  235 5 2 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 235 (accept_3_3 8 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  235 (Polychromatic418967fa.accept_18_7_16_1_1_4951 7 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 70 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 70 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 70 235 5 1 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 70 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 70
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 235 (accept_3_3 2 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 235
  (allA_succ_of_accept 68 69 235 (accept_3_3 68 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 235 (accept_3_3 65 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 235 (accept_3_3 62 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 235 (Polychromatic418967fa.accept_19_3_12_7_1_10004 60 69 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 235 (accept_3_3 59 69 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 235 (accept_3_3 56 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 235 (Polychromatic418967fa.accept_13_3_4_1_1_363 55 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 235 (accept_3_3 53 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 235 (accept_3_3 50 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 235 (accept_3_3 47 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 235 (accept_3_3 44 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 235 (accept_3_3 41 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 235 (accept_3_3 38 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 235 (accept_3_3 35 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 235 (accept_3_3 32 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 235 (accept_3_3 29 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 235 (accept_3_3 26 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 235 (accept_3_3 23 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 235 (accept_3_3 20 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 235 (accept_3_3 17 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 235 (accept_3_3 14 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 235 (accept_3_3 11 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 235 (accept_3_3 8 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 235 (accept_3_3 5 69 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 235 (accept_3_3 2 69 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 1
  69 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 235 (allA_of_3_1 68 68 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 235 (allA_succ_of_accept 66 67 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 235 (accept_3_3 65 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 235 (Polychromatic418967fa.accept_13_12_2_1_1_2909 64 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 235 (accept_3_3 62 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 235 (accept_3_3 59 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 58 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 235 (accept_3_3 56 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 235 (Polychromatic418967fa.accept_13_3_2_1_1_2907 55 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 235
  (Polychromatic418967fa.accept_16_6_3_11_1_3751 54 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 235 (accept_3_3 53 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 235 (accept_3_3 50 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 235 (Polychromatic418967fa.accept_15_4_7_10_1_807 49 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 235 (accept_3_3 47 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 46 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 235 (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 235 (accept_3_3 44 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 235 (accept_3_3 41 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 235 (Polychromatic418967fa.accept_16_8_3_11_1_4763 40 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 235 (accept_3_3 38 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 235 (Polychromatic418967fa.accept_19_18_10_7_1_3174 37 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 235
  (Polychromatic418967fa.accept_17_2_16_14_1_2116 36 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 235 (accept_3_3 35 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 235 (accept_3_3 32 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 235 (accept_3_3 29 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 235 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 235 (accept_3_3 26 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 235 (accept_3_3 23 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 235 (Polychromatic418967fa.accept_10_2_7_5_1_605 22 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 235 (accept_3_3 20 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 235 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 235
  (Polychromatic418967fa.accept_10_8_7_5_1_602 18 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 235 (accept_3_3 17 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 235 (accept_3_3 14 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 235 (accept_3_3 11 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 235 (Polychromatic418967fa.accept_18_10_13_1_1_7736 10 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 235 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 235 (accept_3_3 8 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 235 (accept_3_3 5 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  235 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 67 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 235 (accept_3_3 2 67 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 67 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 235 (allA_succ_of_accept 65 66
  235 (accept_3_3 65 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 64 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 235 (Polychromatic418967fa.accept_14_7_10_11_1_8112 63 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 235 (accept_3_3 62 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 60
  66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 235 (accept_3_3 59 66
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 235
  (Polychromatic418967fa.accept_9_4_3_1_1_154 58 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 66 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 235 (accept_3_3 56 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 66 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 54
  66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 235 (accept_3_3 53 66
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 235
  (Polychromatic418967fa.accept_9_7_3_1_1_386 52 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 66 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 235 (accept_3_3 50 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 66 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 48
  66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 235 (accept_3_3 47 66
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 235
  (Polychromatic418967fa.accept_15_1_6_10_1_23 46 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 66 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 235 (accept_3_3 44 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 66 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 42
  66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 235 (accept_3_3 41 66
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 235
  (Polychromatic418967fa.accept_9_4_3_1_1_154 40 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 66 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 235 (accept_3_3 38 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 66 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 36
  66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 235 (accept_3_3 35 66
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 66 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 235 (accept_3_3 32 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 66 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 235 (Polychromatic418967fa.accept_19_11_9_7_1_4447
  30 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 235 (accept_3_3 29
  66 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 235
  (Polychromatic418967fa.accept_21_7_3_4_1_14091 28 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 66 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 235 (accept_3_3 26 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 66 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 24
  66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 235 (accept_3_3 23 66
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 66 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 235 (accept_3_3 20 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 66 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539
  18 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 235 (accept_3_3 17
  66 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 235
  (Polychromatic418967fa.accept_9_7_3_1_1_386 16 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 66 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 235 (accept_3_3 14 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 66 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 235
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 66 235 (accept_3_3 11 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  66 235 (Polychromatic418967fa.accept_19_10_9_7_1_8696 10 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 66 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 235 (accept_3_3 8 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 66 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 235 (accept_3_3 5 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 66 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 66 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 235 (accept_3_3 2 66 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 66 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 235 (allA_of_3_1 65 65 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 235 (allA_succ_of_accept 63 64 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 235 (accept_3_3 62 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 235 (Polychromatic418967fa.accept_13_8_12_1_1_4662 60 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 235 (accept_3_3 59 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 64 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 235 (accept_3_3 56 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 235 (Polychromatic418967fa.accept_17_4_13_14_1_1139 55 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 64 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 235 (accept_3_3 53 64 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 235 (accept_3_3 50 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 235 (Polychromatic418967fa.accept_22_4_20_15_1_7892 48 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 235 (accept_3_3 47 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 64 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 235 (accept_3_3 44 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 235 (Polychromatic418967fa.accept_20_2_4_15_1_6911 42 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 235 (accept_3_3 41 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 64 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 235 (accept_3_3 38 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 235 (Polychromatic418967fa.accept_13_11_12_1_1_2154 37 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 64 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 235 (accept_3_3 35 64 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 235 (accept_3_3 32 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 235 (Polychromatic418967fa.accept_20_10_4_15_1_12657 30 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 235 (accept_3_3 29 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 235 (Polychromatic418967fa.accept_13_2_12_1_1_343 28 64 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 235 (accept_3_3 26 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 235 (Polychromatic418967fa.accept_20_5_4_15_1_3931 25 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 64 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 235 (accept_3_3 23 64 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 235 (accept_3_3 20 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 235 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 235 (accept_3_3 17 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 64 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 235 (accept_3_3 14 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 235 (Polychromatic418967fa.accept_11_2_9_4_1_310 13 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 64 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 235 (accept_3_3 11 64 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 235 (accept_3_3 8 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  235 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 64 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 64 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 235 (accept_3_3 5 64 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 235 (Polychromatic418967fa.accept_14_4_8_11_1_794 4 64 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 235 (accept_3_3 2 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 64 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 64 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 235
  (allA_succ_of_accept 62 63 235 (accept_3_3 62 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 235 (Polychromatic418967fa.accept_13_9_11_1_1_1375 61 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 63 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 235 (accept_3_3 59 63 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 63 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 235
  (Polychromatic418967fa.accept_10_7_3_5_1_301 57 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 235 (accept_3_3 56 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 235 (Polychromatic418967fa.accept_13_3_11_1_1_2122 55 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 235 (Polychromatic418967fa.accept_15_9_3_10_1_2312 54 63 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 235 (accept_3_3 53 63 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 235
  (Polychromatic418967fa.accept_11_7_8_4_1_718 51 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 235 (accept_3_3 50 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 235 (Polychromatic418967fa.accept_13_10_11_1_1_2152 49 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 63 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 235 (accept_3_3 47 63 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 63 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 235
  (Polychromatic418967fa.accept_11_1_8_4_1_717 45 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 235 (accept_3_3 44 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 235 (Polychromatic418967fa.accept_15_13_3_10_1_2296 43 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 235 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 63 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 235 (accept_3_3 41 63 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 235
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 235 (accept_3_3 38 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 235 (accept_3_3 35 63 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 235 (accept_3_3 32 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 235 (Polychromatic418967fa.accept_14_3_7_11_1_765 31 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 235 (Polychromatic418967fa.accept_20_10_3_15_1_1546 30 63 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 235 (accept_3_3 29 63 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 235
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 235 (accept_3_3 26 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 235 (Polychromatic418967fa.accept_13_12_11_1_1_2920 25 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 235 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 63 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 235 (accept_3_3 23 63 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 63 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 235 (accept_3_3 20 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 235 (Polychromatic418967fa.accept_16_3_15_11_1_2676 19 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 63 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 235 (accept_3_3 17 63 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 235
  (Polychromatic418967fa.accept_17_15_12_14_1_2087 15 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 63 235 (accept_3_3 14 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 235 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 63 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 235 (accept_3_3 11 63 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10
  63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 235 (accept_3_3 8 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  235 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 235 (Polychromatic418967fa.accept_15_6_3_10_1_2341 6 63 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 235 (accept_3_3 5 63 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 235 (Polychromatic418967fa.accept_13_3_11_1_1_2122
  3 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 235 (accept_3_3 2 63
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 235
  (Polychromatic418967fa.accept_11_1_8_4_1_717 1 63 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 235 (allA_of_3_1 62 62
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 235 (allA_succ_of_accept 60 61 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 235 (accept_3_3 59 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 235 (accept_3_3 56 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 61 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 235 (accept_3_3 53 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 235 (accept_3_3 50 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 61 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 235 (accept_3_3 47 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 235 (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 235 (accept_3_3 44 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 61 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 235 (accept_3_3 41 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 235 (accept_3_3 38 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 61 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 235 (accept_3_3 35 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 235 (accept_3_3 32 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 61 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 235 (accept_3_3 29 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 28 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 235 (accept_3_3 26 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 235 (Polychromatic418967fa.accept_20_5_1_15_1_3928 25 61 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 235 (accept_3_3 23 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 235 (accept_3_3 20 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 61 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 235 (accept_3_3 17 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 235 (accept_3_3 14 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 61 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 235 (accept_3_3 11 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 235 (accept_3_3 8 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 61 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 235 (accept_3_3 5 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 61 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 61 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 235 (accept_3_3 2 61 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 235 (allA_succ_of_accept 59 60 235 (accept_3_3 59 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 60 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 235 (accept_3_3 56 60 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 235 5 11 12 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 60 235
  (Polychromatic418967fa.accept_11_10_5_4_1_711 54 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 235 (accept_3_3 53 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 235 (Polychromatic418967fa.accept_13_12_8_1_1_825 51 60 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 235 5 10 12 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 60 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 235 (accept_3_3 47 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 60 235 (Polychromatic418967fa.accept_13_7_8_1_1_2145 46 60 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 235 5 9 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 235 (accept_3_3 44 60 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 60 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 235
  (Polychromatic418967fa.accept_16_10_12_11_1_346 42 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 235 (accept_3_3 41 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60
  235 5 8 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  60 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 235 (accept_3_3 38 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 60 235 (Polychromatic418967fa.accept_13_11_8_1_1_3815 37 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 235 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 60
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 60 235 5 7 12 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 235
  (Polychromatic418967fa.accept_9_7_6_1_1_709 34 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 60 235 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 235 (accept_3_3 32 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 60 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 60 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 235 5 6 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 235 (accept_3_3 29 60 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 235 (Polychromatic418967fa.accept_21_7_18_4_1_5024 28 60 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 235
  (Polychromatic418967fa.accept_18_9_6_1_1_3687 27 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 60 235 (accept_3_3 26 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60
  235 5 5 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  60 235 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 60 235 (accept_3_3 23 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 60 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 235 5 4 12 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 235
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 19 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 60 235 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 235 (accept_3_3 17 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 60 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 60 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 235 5 3 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 235 (accept_3_3 14 60 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 60 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 235 (accept_3_3 11 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60
  235 5 2 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  60 235 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 235 (accept_3_3 8 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 235 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 60 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 60 235 5 1 12 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 4 60 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 235 (accept_3_3 2 60 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 235 (Polychromatic418967fa.accept_14_1_4_11_1_3036 1 60 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 235 (allA_of_3_1 59 59 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 235
  (allA_succ_of_accept 57 58 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 235 (accept_3_3 56 58 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 54
  58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 235 (accept_3_3 53 58
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 235
  (Polychromatic418967fa.accept_9_7_4_1_1_391 52 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 58 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 235 (accept_3_3 50 58 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 48
  58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 235 (accept_3_3 47 58
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 235
  (Polychromatic418967fa.accept_13_7_6_1_1_368 46 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 58 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 235 (accept_3_3 44 58 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 58 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 42
  58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 235 (accept_3_3 41 58
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 40 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 58 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 235 (accept_3_3 38 58 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 58 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 235
  (Polychromatic418967fa.accept_20_16_18_15_1_11357 36 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 58 235 (accept_3_3 35 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 58 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 58 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 235 (accept_3_3 32 58 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 235 (Polychromatic418967fa.accept_13_5_6_1_1_822
  31 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 235 (accept_3_3 29 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 235 (accept_3_3 26 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 235 (accept_3_3 23 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 235 (accept_3_3 20 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 58 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 235
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 235 (accept_3_3 17 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 235 (accept_3_3 14 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 235 (accept_3_3 11 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 235 (Polychromatic418967fa.accept_17_10_7_14_1_4244 10 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 235 (accept_3_3 8 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 58 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 235 (accept_3_3 5 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  235 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 58 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 58 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 235 (accept_3_3 2 58 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 235 (allA_succ_of_accept 56 57 235
  (accept_3_3 56 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 235
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 55 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 235 (accept_3_3 53 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 51
  57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 235 (accept_3_3 50 57
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 235
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 235 (accept_3_3 47 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 45
  57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 235 (accept_3_3 44 57
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 235
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 235 (accept_3_3 41 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 235 (Polychromatic418967fa.accept_11_6_2_4_1_1703
  39 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 235 (accept_3_3 38
  57 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 235
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 37 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 235 (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 235 (accept_3_3 35 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 33
  57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 235 (accept_3_3 32 57
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 235 (accept_3_3 29 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 235 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 235 (accept_3_3 26
  57 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 235
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 235 (accept_3_3 23 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 235 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  21 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 235 (accept_3_3 20
  57 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 235 (accept_3_3 17 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 15
  57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 235 (accept_3_3 14 57
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 235
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 235 (accept_3_3 11 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 235 (Polychromatic418967fa.accept_11_9_2_4_1_707 9
  57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 235 (accept_3_3 8 57 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 235 (accept_3_3 5 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 235 (accept_3_3 2 57 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 235 (Polychromatic418967fa.accept_24_1_9_19_1_12488 1 57 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 235 (allA_of_3_1 56 56 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 235
  (allA_succ_of_accept 54 55 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 235 (accept_3_3 53 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 55 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 51
  55 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 235 5 10 11 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 235
  (Polychromatic418967fa.accept_21_7_13_4_1_2169 49 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 235 (Polychromatic418967fa.accept_19_10_17_7_1_12725 48 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 235 (accept_3_3 47 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 235 (Polychromatic418967fa.accept_13_7_3_1_1_814 46 55 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 235 5 9 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 235 (accept_3_3 44 55 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 235 (Polychromatic418967fa.accept_13_4_3_1_1_2898 43 55 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 235
  (Polychromatic418967fa.accept_23_19_9_5_1_14090 42 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 235 (accept_3_3 41 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  235 5 8 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 235 (Polychromatic418967fa.accept_21_18_13_4_1_14089 39 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 235 (accept_3_3 38 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 55 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 235 5 7 11 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 235
  (Polychromatic418967fa.accept_16_2_7_11_1_1698 34 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 235 (accept_3_3 32 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 235 5 6 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 235 (accept_3_3 29 55 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 55 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 235
  (Polychromatic418967fa.accept_21_6_13_4_1_6521 27 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 235 (accept_3_3 26 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  235 5 5 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 235 (accept_3_3 23 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 235 (Polychromatic418967fa.accept_21_1_13_4_1_11180 22 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 235 (Polychromatic418967fa.accept_16_5_7_11_1_2664 21 55
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 235 5 4 11 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 235 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 235 (accept_3_3 17 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 55 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 235 5 3 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 235 (accept_3_3 14 55 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 235 (Polychromatic418967fa.accept_17_13_4_14_1_4272 13 55 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 235 (accept_3_3 11 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  235 5 2 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 55 235 (accept_3_3 8 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 55 235 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 235 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 55 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 235 5 1 11 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 55 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 235 (accept_3_3 2 55 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 235 (Polychromatic418967fa.accept_17_1_4_14_1_8058 1 55 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 235 (allA_succ_of_accept 53 54 235 (accept_3_3 53 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 235 (Polychromatic418967fa.accept_16_4_6_11_1_3753 52 54 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 54 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 54 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 235 (accept_3_3 50 54 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 235 (accept_3_3 47 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 235 (accept_3_3 44 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 54 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 235
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 42 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 235 (accept_3_3 41 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 235 (Polychromatic418967fa.accept_17_6_3_14_1_2078 40 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 235 (accept_3_3 38 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 235 (accept_3_3 35 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 235 (accept_3_3 32 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 54 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 235 (accept_3_3 29 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 235 (Polychromatic418967fa.accept_17_11_3_14_1_6736 28 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 235 (accept_3_3 26 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 235
  (Polychromatic418967fa.accept_21_3_12_4_1_8116 24 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 235 (accept_3_3 23 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 235 (accept_3_3 20 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 54 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 235
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 235 (accept_3_3 17 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 235 (accept_3_3 14 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 235
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 235 (accept_3_3 11 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 235 (Polychromatic418967fa.accept_19_10_16_7_1_10039 10 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 235 (accept_3_3 8 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 235 (Polychromatic418967fa.accept_21_7_12_4_1_6493 7 54 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 235 (accept_3_3 5 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  235 (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 54 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 235 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 235 (accept_3_3 2 54 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 235 (allA_of_3_1 53 53 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 235 (allA_succ_of_accept 51 52 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 235 (accept_3_3 50 52 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 49
  52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 235 (accept_3_3 47 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 235 (accept_3_3 44 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 52 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 235 (accept_3_3 41 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 235 (accept_3_3 38 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 52 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 235 (accept_3_3 35 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 235 (accept_3_3 32 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 52 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 235 (accept_3_3 29 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 235 (accept_3_3 26 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 235 (Polychromatic418967fa.accept_16_9_4_11_1_2661 25 52 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 235 (accept_3_3 23 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 235 (accept_3_3 20 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 235 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 52 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 235
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 235 (accept_3_3 17 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 235 (accept_3_3 14 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 52 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 235 (accept_3_3 11 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 235 (accept_3_3 8 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 52 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 235 (accept_3_3 5 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 52 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 235 (accept_3_3 2 52 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 52 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 235))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 235 (allA_succ_of_accept 50 51 235 (accept_3_3 50 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 51 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 235 (accept_3_3 47 51 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 235 (accept_3_3 44 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 235 (Polychromatic418967fa.accept_15_12_6_10_1_1516 42 51 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 235 (accept_3_3 41 51 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 235 (accept_3_3 38 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 235 (Polychromatic418967fa.accept_13_11_12_1_1_2154 37 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 235 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 51 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 235 (accept_3_3 35 51 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 235 (accept_3_3 32 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 51 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 235 (accept_3_3 29 51 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 235 (accept_3_3 26 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 51 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 235 (accept_3_3 23 51 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 235 (accept_3_3 20 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 235 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 51 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 235 (accept_3_3 17 51 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 235
  (Polychromatic418967fa.accept_13_2_12_1_1_343 15 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 235 (accept_3_3 14 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 235 (accept_3_3 11 51 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 51 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 235
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 235 (accept_3_3 8 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 235 (accept_3_3 5 51 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 51
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 235 (accept_3_3 2 51 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 1
  51 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  235))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 235 (allA_of_3_1 50 50 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 235 (allA_succ_of_accept 48 49 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 235 (accept_3_3 47 49 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 235
  (Polychromatic418967fa.accept_14_3_7_11_1_765 45 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 235 (accept_3_3 44 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 235 (accept_3_3 41 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 235 (Polychromatic418967fa.accept_17_6_15_14_1_8027 40 49 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 235 (accept_3_3 38 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 235 (Polychromatic418967fa.accept_13_11_10_1_1_1409 37 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 235 (accept_3_3 35 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 235 (accept_3_3 32 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 235 (accept_3_3 29 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 49 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 235
  (Polychromatic418967fa.accept_19_8_11_7_1_11474 27 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 235 (accept_3_3 26 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 235 (accept_3_3 23 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 235 (accept_3_3 20 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 235 (Polychromatic418967fa.accept_21_19_7_4_1_4994 19 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 235 (accept_3_3 17 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 235 (accept_3_3 14 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 235 (accept_3_3 11 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 235
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 235 (accept_3_3 8 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 235 (accept_3_3 5 49 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 49 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 49
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 235 (accept_3_3 2 49 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 1
  49 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  235))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 235 (allA_succ_of_accept 47 48 235 (accept_3_3 47
  48 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 235
  (Polychromatic418967fa.accept_25_21_23_10_1_14088 46 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 48 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 235 (accept_3_3 44 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 48 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 235 (accept_3_3 41 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  48 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 235 (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 48 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 235 (accept_3_3 38 48 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 235
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 235 (accept_3_3 35 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 235 (accept_3_3 32 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 235 (accept_3_3 29 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 28 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 235 (accept_3_3 26 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 48 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 235 (accept_3_3 23 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 235 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 235 (accept_3_3 20 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 235
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 235 (accept_3_3 17 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 235 (accept_3_3 14 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 235 (accept_3_3 11 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 235 (accept_3_3 8 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 235 (accept_3_3 5 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 48 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 235 (accept_3_3 2 48 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 235 (Polychromatic418967fa.accept_19_1_10_7_1_14087 1 48 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 235)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 235 (allA_of_3_1 47 47 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 235 (allA_succ_of_accept 45 46
  235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 235 (accept_3_3 44 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 235 (Polychromatic418967fa.accept_14_1_4_11_1_3036 43 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 235 (Polychromatic418967fa.accept_11_9_2_4_1_707 42 46 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 235 (accept_3_3 41 46 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 46 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 235 (accept_3_3 38 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 235 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 46 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 235 (accept_3_3 35 46 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 46 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 235 (accept_3_3 32 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 235 (Polychromatic418967fa.accept_19_11_8_7_1_11423 30 46 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 235 (accept_3_3 29 46 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 235 (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 46 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 235 (accept_3_3 26 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 46 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 235 (accept_3_3 23 46 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 235 (Polychromatic418967fa.accept_14_8_4_11_1_3035 22 46 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 235 (accept_3_3 20 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 235 (Polychromatic418967fa.accept_19_18_8_7_1_4446 18 46 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 235 (accept_3_3 17 46 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 46 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 235 (accept_3_3 14 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 235 (Polychromatic418967fa.accept_19_12_8_7_1_7209 12 46 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 235 (accept_3_3 11 46 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 235 (Polychromatic418967fa.accept_20_10_6_15_1_5381 10 46
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 235 (accept_3_3 8 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  235 (Polychromatic418967fa.accept_14_7_4_11_1_3038 7 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 46 235 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 46 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 235 (accept_3_3 5 46 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 46 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 46 235 (accept_3_3 2 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46
  235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 235)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 235 (allA_succ_of_accept 44 45 235
  (accept_3_3 44 45 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 45 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 235 (accept_3_3 41 45 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 45 235 5 8 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 45 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 45 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 235 (accept_3_3 38 45 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 235 (Polychromatic418967fa.accept_17_3_11_14_1_2071 37 45 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 45 235 5 7 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 45 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 235 (Polychromatic418967fa.accept_13_7_6_1_1_368 33 45 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 235 (accept_3_3 32 45 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 235 (Polychromatic418967fa.accept_13_5_6_1_1_822
  31 45 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 235 5 6 9 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 235 (accept_3_3 29
  45 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 45 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 235 (accept_3_3 26 45 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 45 235 5 5 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 45 235 (Polychromatic418967fa.accept_16_8_13_11_1_4772 24 45 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 235 (accept_3_3 23 45 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 235
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 45 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 45 235 5 4 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 235 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 45 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 235 (accept_3_3 17 45 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  45 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 235 5 3 9 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 235 (accept_3_3 14
  45 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 45 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 235 (Polychromatic418967fa.accept_17_12_11_14_1_3120 12 45 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 235 (accept_3_3 11 45 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 45 235 5 2 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 45 235 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 45 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 235 (accept_3_3 8 45 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 235 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 45 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 45 235 5 1 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 45 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 235 (accept_3_3 2 45 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  45 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  235))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 235 (allA_of_3_1 44 44 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 235 (allA_succ_of_accept 42 43 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 43 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 235 (accept_3_3 41 43 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 40
  43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 235 (accept_3_3 38 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 235 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 43 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 235 (accept_3_3 35 43 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 34 43
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 235 (accept_3_3 32 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 43 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 235 (accept_3_3 29 43 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 43 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 235
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 235 (accept_3_3 26 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 235 (Polychromatic418967fa.accept_19_6_5_7_1_8708 25 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 235 (accept_3_3 23 43 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 43 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 235 (accept_3_3 20 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 43 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 235 (accept_3_3 17 43 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 235 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 43 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 235 (accept_3_3 14 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 235 (accept_3_3 11 43 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 43 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 235
  (Polychromatic418967fa.accept_19_9_5_7_1_5853 9 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 235 (accept_3_3 8 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  235 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 43 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 235 (accept_3_3 5 43 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 43 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 235 (accept_3_3 2 43 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507
  1 43 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  235))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 235 (allA_succ_of_accept 41 42 235 (accept_3_3 41 42 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 40
  42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 42 235 (accept_3_3 38 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  42 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 42 235 (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 42 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 235 (accept_3_3 35 42 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 42 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 42 235 (accept_3_3 32 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  42 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 42 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 42 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 235 (accept_3_3 29 42 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 42 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 42 235
  (Polychromatic418967fa.accept_10_7_2_5_1_298 27 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 42 235 (accept_3_3 26 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  42 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 42 235 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 42 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 235 (accept_3_3 23 42 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 42 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 42 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 42 235 (accept_3_3 20 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  42 235 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 42 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 42 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 235 (accept_3_3 17 42 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 42 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 235
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 15 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 42 235 (accept_3_3 14 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  42 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 42 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 42 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 235 (accept_3_3 11 42 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 235 (Polychromatic418967fa.accept_20_10_2_15_1_1517 10 42 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 42 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 235 (accept_3_3 8 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42
  235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 42 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 42 235 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 42 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 235 (accept_3_3 5 42 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 42 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 42 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 42
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 235 (accept_3_3 2 42 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  235)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 235 (allA_of_3_1 41 41 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 235 (allA_succ_of_accept 39 40 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 40 235 (accept_3_3 38 40 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 40 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 37
  40 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 40 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 40 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 40 235 5 7 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 40 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 40 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 235 (accept_3_3 32 40 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 40 235
  (Polychromatic418967fa.accept_21_10_19_4_1_8121 31 40 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 235 5 6 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 235 (accept_3_3 29 40 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  40 235 (Polychromatic418967fa.accept_16_12_8_11_1_2695 28 40 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 40 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 235 (accept_3_3 26 40 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 40 235 5 5 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 40 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 40 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 235 (accept_3_3 23 40 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 40 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 235 5 4 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 235 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 40 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 235 (Polychromatic418967fa.accept_21_18_19_4_1_4979 18 40
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 235 (accept_3_3 17 40 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16
  40 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 40 235 5 3 8 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 40 235 (accept_3_3 14
  40 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 40 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 40 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 40 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 235 (accept_3_3 11 40 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 40 235 5 2 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 40 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 235 (accept_3_3 8 40 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 40 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 40 235 5 1 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 40 235 (Polychromatic418967fa.accept_16_4_8_11_1_5961 4 40 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 235 (accept_3_3 2 40 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1
  40 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  235)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 235 (allA_succ_of_accept 38 39 235 (accept_3_3 38 39 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 235 (Polychromatic418967fa.accept_16_5_7_11_1_2664
  37 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 235 (accept_3_3 35 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 39 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 235 (accept_3_3 32 39 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 39 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 235
  (Polychromatic418967fa.accept_18_12_3_1_1_3685 30 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 235 (accept_3_3 29 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 235 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 39 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 235 (accept_3_3 26 39 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 39 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 235 (accept_3_3 23 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 39 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 235 (accept_3_3 20 39 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 235 (Polychromatic418967fa.accept_15_4_9_10_1_5384 19 39 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 235
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 235 (accept_3_3 17 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 39 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 235 (accept_3_3 14 39 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 39 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 235 (accept_3_3 11 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 235 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 39 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 235 (accept_3_3 8 39 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 39 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 235 (accept_3_3 5 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 235 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 39 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 235 (accept_3_3 2 39 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 39 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 235))))))))))))))))))))))))))))))))))))))) (allB_succ 38 235
  (allA_of_3_1 38 38 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 235 (allA_succ_of_accept 36 37 235
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 235 (accept_3_3 35 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 37 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 235 (accept_3_3 32 37 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 37 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 235 (accept_3_3 29 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 37 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 235 (accept_3_3 26 37 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 235 (Polychromatic418967fa.accept_13_12_11_1_1_2920 25 37 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 235
  (Polychromatic418967fa.accept_16_8_5_11_1_4776 24 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 235 (accept_3_3 23 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 235 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 37 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 235 (accept_3_3 20 37 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 37 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 235 (accept_3_3 17 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 235 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 235 (Polychromatic418967fa.accept_17_15_3_14_1_4230 15 37 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 235 (accept_3_3 14 37 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 235 (accept_3_3 11 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 235 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 37 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 235 (accept_3_3 8 37 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 235 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 37 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 235 (accept_3_3 5 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  235 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 37 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 37 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 37 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 235 (accept_3_3 2 37 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 37 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 235))))))))))))))))))))))))))))))))))))) (allB_succ
  36 235 (allA_succ_of_accept 35 36 235 (accept_3_3 35 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 36 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 235 (accept_3_3 32 36 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31
  36 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 235
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 235 (accept_3_3 29 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 235 (Polychromatic418967fa.accept_16_12_4_11_1_3710 28 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 235 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 36 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 235 (accept_3_3 26 36 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 235 (Polychromatic418967fa.accept_16_9_4_11_1_2661 25 36
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 235 (accept_3_3 23 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 235 (Polychromatic418967fa.accept_13_9_10_1_1_1389 22 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 36 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 235 (accept_3_3 20 36 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 235
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 235 (accept_3_3 17 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 16 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 235 (accept_3_3 14 36 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 235 (Polychromatic418967fa.accept_19_13_17_7_1_12726 13 36 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 235 (accept_3_3 11 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 36 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 235 (accept_3_3 8 36 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 235
  (Polychromatic418967fa.accept_16_6_4_11_1_1719 6 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 235 (accept_3_3 5 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  235 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 36 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 36 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 235 (accept_3_3 2 36 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 36 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 36 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 235)))))))))))))))))))))))))))))))))))) (allB_succ 35 235
  (allA_of_3_1 35 35 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 235 (allA_succ_of_accept 33 34 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 235 (accept_3_3 32 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 34 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 235 (accept_3_3 29 34 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 34 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 235 (accept_3_3 26 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 34 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 235 (accept_3_3 23 34 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 34 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 235 (accept_3_3 20 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 235 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 34 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 235 (accept_3_3 17 34 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 34 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 235 (accept_3_3 14 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 34 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 235 (accept_3_3 11 34 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 34 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 235 (accept_3_3 8 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  235 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 34 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 34 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 235 (accept_3_3 5 34 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 34 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 235 (accept_3_3 2 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34
  235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 235)))))))))))))))))))))))))))))))))) (allB_succ 33 235 (allA_succ_of_accept 32 33 235 (accept_3_3 32 33
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 33 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 33 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 235 (accept_3_3 29 33 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 33 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 27
  33 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 235 (accept_3_3 26 33
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 235
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 33 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 33 235 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 33 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 235 (accept_3_3 23 33 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 33 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 21
  33 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 235 (accept_3_3 20 33
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 235
  (Polychromatic418967fa.accept_13_6_7_1_1_335 19 33 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 33 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 235 (accept_3_3 17 33 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 33 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  33 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 235 (accept_3_3 14 33
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 33 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 33 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 33 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 235 (accept_3_3 11 33 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 33 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  33 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 235 (accept_3_3 8 33 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7
  33 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 235 (accept_3_3 5 33 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 33 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 235 (accept_3_3 2 33 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 33 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 235))))))))))))))))))))))))))))))))) (allB_succ 32 235
  (allA_of_3_1 32 32 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 235 (allA_succ_of_accept 30 31 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 235 (accept_3_3 29 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 31 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 235 (accept_3_3 26 31 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 31 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 235 (accept_3_3 23 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 31 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 235 (accept_3_3 20 31 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 31 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 235
  (Polychromatic418967fa.accept_19_18_12_7_1_4432 18 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 235 (accept_3_3 17 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 31 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 235 (accept_3_3 14 31 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 31 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 235 (accept_3_3 11 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 235 (Polychromatic418967fa.accept_16_10_15_11_1_3785 10 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 31 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 235 (accept_3_3 8 31 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 235 (accept_3_3 5 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  235 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 31 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 31 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 235 (accept_3_3 2 31 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 31 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 235))))))))))))))))))))))))))))))) (allB_succ 30 235
  (allA_succ_of_accept 29 30 235 (accept_3_3 29 30 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 235 (Polychromatic418967fa.accept_19_9_11_7_1_5836 28 30 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 30 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 235 (accept_3_3 26 30 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 30 235 5 5 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 30 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 30 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 235 (accept_3_3 23 30 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 30 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 30 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 235 5 4 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 30 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 30 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 235 (accept_3_3 17 30 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 16
  30 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 235 5 3 6 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 235 (accept_3_3 14
  30 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 30 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 30 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 235 (accept_3_3 11 30 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 30 235 5 2 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 30 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 235 (accept_3_3 8 30 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 30 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 30 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 30 235 5 1 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 30 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 30 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 235 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 30 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 235 (accept_3_3 2 30 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 235))))))))))))))))))))))))))))))
  (allB_succ 29 235 (allA_of_3_1 29 29 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 235
  (allA_succ_of_accept 27 28 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 235 (accept_3_3 26 28 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 235 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 28 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 235
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 28 235 (accept_3_3 23 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  28 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 28 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 235 (accept_3_3 20 28 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 235 (Polychromatic418967fa.accept_13_6_2_1_1_2137 19 28 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 235
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 235 (accept_3_3 17 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  28 235 (Polychromatic418967fa.accept_13_3_2_1_1_2907 16 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 235 (accept_3_3 14 28 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 28 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 28 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 235
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 235 (accept_3_3 11 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 235 (accept_3_3 8 28 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 28 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 235
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 235 (accept_3_3 5 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 28 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 28 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 235 (accept_3_3 2 28 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 28 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 235)))))))))))))))))))))))))))) (allB_succ 27 235
  (allA_succ_of_accept 26 27 235 (accept_3_3 26 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  27 235 (Polychromatic418967fa.accept_19_6_8_7_1_10023 25 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 27 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 235 (accept_3_3 23 27 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 27 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 235
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 235 (accept_3_3 20 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 27 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 235 (accept_3_3 17 27 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 235
  (Polychromatic418967fa.accept_19_15_8_7_1_11482 15 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 235 (accept_3_3 14 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 235 (accept_3_3 11 27 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 235 (accept_3_3 8 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  235 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 235 (Polychromatic418967fa.accept_15_6_12_10_1_1543 6 27 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 235 (accept_3_3 5 27 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 235 (accept_3_3 2 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  235 (Polychromatic418967fa.accept_17_1_10_14_1_1173 1 27 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 235))))))))))))))))))))))))))) (allB_succ 26 235 (allA_of_3_1 26 26 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 235 (allA_succ_of_accept 24 25 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 24
  25 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 235 (accept_3_3 23 25
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 235 (Polychromatic418967fa.accept_4_2_1_3_1_27
  22 25 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 25 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 25 235 5 4 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 25 235 (Polychromatic418967fa.accept_20_19_5_15_1_5380 19 25 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 235 (accept_3_3 17 25 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 235
  (Polychromatic418967fa.accept_17_16_8_14_1_6757 16 25 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 25 235 5 3 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 25 235 (accept_3_3 14 25 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 25 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 25 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 235 (accept_3_3 11 25 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 235 5 2 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 25 235 (Polychromatic418967fa.accept_20_9_5_15_1_3965 9 25 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 235 (accept_3_3 8 25 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 25 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 235 5 1 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 25 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 235 (accept_3_3 2 25 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 235 (Polychromatic418967fa.accept_19_1_6_7_1_2019 1
  25 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 235)))))))))))))))))))))))))
  (allB_succ 24 235 (allA_succ_of_accept 23 24 235 (accept_3_3 23 24 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 24 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 235 (accept_3_3 20 24 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 235 (Polychromatic418967fa.accept_10_9_4_5_1_616
  19 24 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 235
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 24 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 235 (accept_3_3 17 24 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 24 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 235 (accept_3_3 14 24 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 24 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 235 (accept_3_3 11 24 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 235 (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 24 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 24 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 235 (accept_3_3 8 24 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 24 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 235 (accept_3_3 5 24 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  235 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 24 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 235 (accept_3_3 2 24 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 235)))))))))))))))))))))))) (allB_succ 23 235 (allA_of_3_1 23 23
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 235 (allA_succ_of_accept 21 22 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 235 (accept_3_3 20 22 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 22 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 22 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 235 (accept_3_3 17 22 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 22 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 235 (accept_3_3 14 22 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 22 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 235 (accept_3_3 11 22 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 22 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 235 (accept_3_3 8 22 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 22 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 22 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 235 (accept_3_3 5 22 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 22 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 235 (accept_3_3 2 22 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 235)))))))))))))))))))))) (allB_succ 21
  235 (allA_succ_of_accept 20 21 235 (accept_3_3 20 21 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 21 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 235 (accept_3_3 17 21 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 21 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 235 (accept_3_3 14 21 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 21 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 235 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 21 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 235 (accept_3_3 11 21 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 235
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 21 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 235 (accept_3_3 8 21 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 21 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 235 (accept_3_3 5 21 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 3
  21 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 235 (accept_3_3 2 21 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 1
  21 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 235))))))))))))))))))))) (allB_succ
  20 235 (allA_of_3_1 20 20 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 235 (allA_succ_of_accept 18 19
  235 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 19 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 235 (accept_3_3 17 19 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 19 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 19 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 235 (accept_3_3 14 19 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  19 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 235
  (Polychromatic418967fa.accept_11_1_8_4_1_717 12 19 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 235 (accept_3_3 11 19 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 235 (Polychromatic418967fa.accept_20_10_19_15_1_2692 10 19 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 19 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 235 (accept_3_3 8 19 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 19 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 19 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 235 (accept_3_3 5 19 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  235 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 19 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 235 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 19 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 235 (accept_3_3 2 19 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 19 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 235))))))))))))))))))) (allB_succ 18 235 (allA_succ_of_accept 17
  18 235 (accept_3_3 17 18 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 235
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 18 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 235 (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 18 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 235 (accept_3_3 14 18 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 235 (Polychromatic418967fa.accept_10_2_8_5_1_587
  12 18 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 235 (accept_3_3 11
  18 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 235
  (Polychromatic418967fa.accept_17_10_1_14_1_489 10 18 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 18 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 235 (accept_3_3 8 18 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 18 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 18 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 235 (Polychromatic418967fa.accept_13_6_5_1_1_834 6
  18 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 235 (accept_3_3 5 18 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 235 (Polychromatic418967fa.accept_13_4_5_1_1_833 4
  18 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 235
  (Polychromatic418967fa.accept_10_3_8_5_1_606 3 18 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 235 (accept_3_3 2 18 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18
  235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 235)))))))))))))))))) (allB_succ 17 235 (allA_of_3_1 17 17 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 235 (allA_succ_of_accept 15 16 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 235 (accept_3_3 14 16 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 16 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 16 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 235 (accept_3_3 11 16 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 235 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 16 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 235 (accept_3_3 8 16 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 235 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 16 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 16 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 235 (accept_3_3 5 16 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 16 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 235 (accept_3_3 2 16 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 16 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 235)))))))))))))))) (allB_succ 15 235 (allA_succ_of_accept 14 15
  235 (accept_3_3 14 15 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 15 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 235 (accept_3_3 11 15 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 15 235 5 2 3 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 15 235 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 15 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 235 (accept_3_3 8 15 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 15 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 235
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 15 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 235 5 1 3 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 235 (accept_3_3 2 15 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 235 (Polychromatic418967fa.accept_16_1_15_11_1_356
  1 15 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 235))))))))))))))) (allB_succ 14
  235 (allA_of_3_1 14 14 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 235 (allA_succ_of_accept 12 13 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 235 (accept_3_3 11 13 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 13 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 235 (accept_3_3 8 13 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 235 (accept_3_3 5 13 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 13 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 13 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 235 (accept_3_3 2 13 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 13 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 235))))))))))))) (allB_succ 12 235
  (allA_succ_of_accept 11 12 235 (accept_3_3 11 12 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  12 235 (Polychromatic418967fa.accept_16_10_12_11_1_346 10 12 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 235 (accept_3_3 8 12 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 12 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 235 (accept_3_3 5 12 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12
  235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 12 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 12 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 12 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 235 (accept_3_3 2 12 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 12 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 235)))))))))))) (allB_succ 11 235 (allA_of_3_1 11 11 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 235 (allA_succ_of_accept 9 10 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 235 (accept_3_3 8 10 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  235 (Polychromatic418967fa.accept_14_7_10_11_1_8112 7 10 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 10 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 10 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 10 235 5 1 2 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 10 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 4
  10 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 10 235 (accept_3_3 2 10 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10
  235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 235)))))))))) (allB_succ 9 235 (allA_succ_of_accept 8 9 235 (accept_3_3 8 9 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 235 (Polychromatic418967fa.accept_22_7_9_15_1_14086 7 9 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 235 (accept_3_3 5 9 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 9 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 235 (accept_3_3 2 9 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 9 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 235))))))))) (allB_succ 8 235 (allA_of_3_1 8 8 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 235 (allA_succ_of_accept 6 7 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 7 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 235 (accept_3_3 5 7 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 7 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 7 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 235 (accept_3_3 2 7 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 7 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 235))))))) (allB_succ 6 235 (allA_succ_of_accept 5 6 235
  (accept_3_3 5 6 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 4 6 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 235 (accept_3_3 2 6 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 235)))))) (allB_succ 5 235 (allA_of_3_1 5 5 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 235 (allA_succ_of_accept 3 4 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 235 (accept_3_3 2 4 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 235
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 4 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 235)))) (allB_succ 3 235 (allA_succ_of_accept 2 3 235 (accept_3_3 2 3 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 3 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 235))) (allB_succ 2 235 (allA_of_3_1 2 2 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


