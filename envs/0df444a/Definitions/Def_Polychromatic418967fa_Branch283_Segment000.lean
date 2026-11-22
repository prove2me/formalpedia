-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch283_Segment000
-- name    : Polychromatic418967fa_Branch283_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:53:32.928524+00:00
-- url     : https://prove2.me/theorems/93ebf177-3024-45e1-ab8b-6ac32fc2093f
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

def Polychromatic418967fa.branch_283_segment_000 : allB 123 283 :=
  allB_succ 122 283 (allA_of_3_1 122 122 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 121 283
  (allA_succ_of_accept 120 121 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 120 121 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 283 (accept_3_3 119 121 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 117 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 121 283 (accept_3_3 116 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 121 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 115 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 283 (accept_3_3 113 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 112 121
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 121 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 111 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 121 283 (accept_3_3 110 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 121 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 109 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 121 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 108 121 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 121 283 (accept_3_3 107 121 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27
  106 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 283
  (Polychromatic418967fa.accept_13_1_4_10_1_622 105 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 121 283 (accept_3_3 104 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 121 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 283 (accept_3_3 101 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 100
  121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 283 (accept_3_3 98 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 283 (accept_3_3 95 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 283
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 93 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 283 (accept_3_3 92 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 283 (Polychromatic418967fa.accept_19_15_7_17_1_5168 91 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 283 (accept_3_3 89 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 88 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 283
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 87 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 121 283 (accept_3_3 86 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 121 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 121 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 121 283 (Polychromatic418967fa.accept_13_6_4_10_1_660 84 121
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 283 (accept_3_3 83 121
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 121 283 (Polychromatic418967fa.accept_19_5_7_17_1_9442 81 121 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 121 283 (accept_3_3 80 121 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 121 283 (Polychromatic418967fa.accept_13_1_4_10_1_622 79 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 121 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 121 283 (accept_3_3 77 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 121 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 121 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 121 283 (accept_3_3 74 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 121 283 (Polychromatic418967fa.accept_13_8_4_10_1_4358 73 121 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 121 283
  (Polychromatic418967fa.accept_10_2_1_3_1_233 72 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 121 283 (accept_3_3 71 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 121 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 121 283 (accept_3_3 68 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 121 283 (Polychromatic418967fa.accept_19_10_7_17_1_9496 67 121 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 121 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 121 283 (accept_3_3 65 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 121 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 121 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 283 (accept_3_3 62 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 121 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 283
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 60 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 121 283 (accept_3_3 59 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 121 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 283 (accept_3_3 56 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 121 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 121 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 121 283 (accept_3_3 53 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 121 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 52 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 121 283 (Polychromatic418967fa.accept_19_13_7_17_1_9441 51 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 283 (accept_3_3 50 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 283 (Polychromatic418967fa.accept_21_7_16_10_1_1349 49 121
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 121 283 (accept_3_3 47 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 121 283 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 283 (accept_3_3 44 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 121 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 121 283 (accept_3_3 41 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 121 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 283 (Polychromatic418967fa.accept_25_14_21_8_1_13902 39 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 283 (accept_3_3 38 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 37 121
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 121 283 (accept_3_3 35 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 121 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 283 (accept_3_3 32 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 121 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 121 283 (accept_3_3 29 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 121 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 121 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 283 (accept_3_3 26 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 121 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 283
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 121 283 (accept_3_3 23 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 283 (Polychromatic418967fa.accept_13_8_4_10_1_4358 21 121
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 283 (accept_3_3 20 121
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 283 (accept_3_3 17 121 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 121 283 (Polychromatic418967fa.accept_19_16_7_17_1_3853 16 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 283 (accept_3_3 14 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 283 (accept_3_3 11 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 283
  (Polychromatic418967fa.accept_17_9_2_11_1_4042 9 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 283 (accept_3_3 8 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 283 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 283 (accept_3_3 5 121 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 283 (Polychromatic418967fa.accept_16_4_9_11_1_7159 4 121 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 283
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 3 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 283 (accept_3_3 2 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 121 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 283 (allA_succ_of_accept 119 120 283 (accept_3_3 119 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 120 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 118 120 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 120 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 117 120
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 283 (accept_3_3 116 120
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 120 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 115 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 120 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 114 120 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 120 283 (accept_3_3 113 120 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 120 283 (Polychromatic418967fa.accept_17_10_1_11_1_2900 112 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 283
  (Polychromatic418967fa.accept_13_7_3_10_1_656 111 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 120 283 (accept_3_3 110 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 120 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 109 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 120 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 108 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 283 (accept_3_3 107 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 106 120
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 120 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 105 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 120 283 (accept_3_3 104 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 120 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 103 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 120 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 120 283 (accept_3_3 101 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 120
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 283
  (Polychromatic418967fa.accept_16_3_8_11_1_2714 99 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 120 283 (accept_3_3 98 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 120 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 97 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 120 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 120 283 (accept_3_3 95 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 283 (Polychromatic418967fa.accept_19_18_6_17_1_8078 94 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 120 283 (accept_3_3 92 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 120 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 120 283 (Polychromatic418967fa.accept_21_6_15_10_1_2579 90 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 120 283 (accept_3_3 89 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 120 283 (accept_3_3 86 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 120 283 (Polychromatic418967fa.accept_13_7_3_10_1_656 85 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 120 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 84 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 120 283 (accept_3_3 83 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 120 283 (accept_3_3 80 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 120 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 120 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 283 (accept_3_3 77 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 283 (Polychromatic418967fa.accept_13_11_3_10_1_4374 76 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 120 283 (accept_3_3 74 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 120 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 120 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 120 283 (accept_3_3 71 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 120 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 120 283 (accept_3_3 68 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 120 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 120 283 (Polychromatic418967fa.accept_19_9_6_17_1_3880 66 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 120 283 (accept_3_3 65 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 283
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 120 283 (accept_3_3 62 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 120 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 120 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 120 283 (accept_3_3 59 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 283 (Polychromatic418967fa.accept_7_2_1_3_1_102
  58 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 283
  (Polychromatic418967fa.accept_18_3_12_13_1_3307 57 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 120 283 (accept_3_3 56 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 120 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 120 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 120 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 120 283 (accept_3_3 53 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 283 (Polychromatic418967fa.accept_9_7_3_4_1_218
  52 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 120 283 (accept_3_3 50 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 120 283 (Polychromatic418967fa.accept_19_11_6_17_1_9455 49 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 120 283 (Polychromatic418967fa.accept_21_6_15_10_1_2579 48 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 283 (accept_3_3 47 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 283
  (Polychromatic418967fa.accept_13_6_3_10_1_698 45 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 120 283 (accept_3_3 44 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 120 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 120 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 120 283 (accept_3_3 41 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 120 283 (accept_3_3 38 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 120 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 120 283 (Polychromatic418967fa.accept_16_4_8_11_1_5961 36 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 120 283 (accept_3_3 35 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 120 283 (accept_3_3 32 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 120 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 120 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 120 283 (accept_3_3 29 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 283
  (Polychromatic418967fa.accept_17_10_1_11_1_2900 27 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 120 283 (accept_3_3 26 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 120 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 120 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 283 (accept_3_3 23 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 283
  (Polychromatic418967fa.accept_19_3_6_17_1_6579 22 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 120 283 (Polychromatic418967fa.accept_16_5_8_11_1_9582 21 120 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 283 (accept_3_3 20 120 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 120 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 283 (Polychromatic418967fa.accept_7_4_1_3_1_277
  18 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 283 (accept_3_3 17
  120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 120 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 120 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 283 (accept_3_3 14 120 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 120 283 (Polychromatic418967fa.accept_16_13_8_11_1_4785 13 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 120 283 (accept_3_3 11 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 120 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 120 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 283 (accept_3_3 8 120 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 120 283 (accept_3_3 5 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  120 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 120 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 120 283 (Polychromatic418967fa.accept_16_3_8_11_1_2714 3 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 283 (accept_3_3 2 120 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 120 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 283 (allA_of_3_1 119 119 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 118 283
  (allA_succ_of_accept 117 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 118 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 118 283 (accept_3_3 116 118 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 118 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 115 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 118 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 114 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 118 283 (accept_3_3 113 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 118 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 112 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 118 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 118 283 (accept_3_3 110 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 109 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 118 283
  (Polychromatic418967fa.accept_13_4_1_10_1_693 108 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 118 283 (accept_3_3 107 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 118 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 106 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 118 283 (accept_3_3 104 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 118 283 (Polychromatic418967fa.accept_19_8_4_17_1_9510 103 118 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 118 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 102 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 118 283 (accept_3_3 101 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 118 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 100 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 118 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 118 283 (accept_3_3 98 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 118 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 96 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 118 283 (accept_3_3 95 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 118 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 94 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 118 283 (accept_3_3 92 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 118 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 91 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 118 283
  (Polychromatic418967fa.accept_17_5_16_11_1_3998 90 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 118 283 (accept_3_3 89 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 118 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 118 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 118 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 118 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 118 283 (accept_3_3 86 118 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85
  118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 118 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 118 283 (accept_3_3 83 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 118 283 (Polychromatic418967fa.accept_13_4_1_10_1_693 82 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 118 283 (accept_3_3 80 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 118 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 118 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 78 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 118 283 (accept_3_3 77 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 118 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 76 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 118 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 283 (accept_3_3 74 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 118 283 (accept_3_3 71 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 118 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 283 (accept_3_3 68 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 283 (accept_3_3 65 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 283 (accept_3_3 62 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 283 (accept_3_3 59 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 283 (accept_3_3 56 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 55 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 283
  (Polychromatic418967fa.accept_22_10_8_19_1_12892 54 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 118 283 (accept_3_3 53 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 118 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 118 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 118 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 118 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 283 (accept_3_3 50 118 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 283 (accept_3_3 47 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 283 (accept_3_3 44 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 283 (accept_3_3 41 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 283 (accept_3_3 38 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 283
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 283 (accept_3_3 35 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 283 (accept_3_3 32 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 283 (accept_3_3 29 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 283 (accept_3_3 26 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 283 (accept_3_3 23 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 283 (Polychromatic418967fa.accept_13_9_1_10_1_647 22 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 283 (accept_3_3 20 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 283 (Polychromatic418967fa.accept_16_3_6_11_1_2718 19 118 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 283 (accept_3_3 17 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 283 (accept_3_3 14 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 283 (accept_3_3 11 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 283 (accept_3_3 8 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 283 (accept_3_3 5 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 118 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 283 (accept_3_3 2 118 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 283 (allA_succ_of_accept 116 117 283 (accept_3_3 116 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 115 117 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 117
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 283 (accept_3_3 113 117
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 112 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 117 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 111 117 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 283 (accept_3_3 110 117 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 117 283 (Polychromatic418967fa.accept_19_14_3_17_1_6558 109 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 108 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 117 283 (accept_3_3 107 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 117 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 117 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 105 117
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 283 (accept_3_3 104 117
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 283
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 103 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 117 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 283 (accept_3_3 101 117 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 117 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 117 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 99 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 117 283 (accept_3_3 98 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 117 283 (Polychromatic418967fa.accept_19_2_3_17_1_5146 97 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 117 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 96 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 283 (accept_3_3 95 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 117 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 117 283 (accept_3_3 92 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 117 283 (Polychromatic418967fa.accept_15_1_12_13_1_944 91 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 283 (accept_3_3 89 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 87 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 117 283 (accept_3_3 86 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 117 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 117 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 84 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 283 (accept_3_3 83 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 283
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 81 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 117 283 (accept_3_3 80 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 117 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 283 (accept_3_3 77 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 283
  (Polychromatic418967fa.accept_10_5_7_3_1_561 75 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 117 283 (accept_3_3 74 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 117 283 (Polychromatic418967fa.accept_16_9_5_11_1_3776 73 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 117 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 283 (accept_3_3 71 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 283
  (Polychromatic418967fa.accept_19_12_3_17_1_5182 69 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 283 (accept_3_3 68 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 283 (Polychromatic418967fa.accept_17_16_15_11_1_10421 67 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 283 (accept_3_3 65
  117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 64 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 117 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 117 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 283 (accept_3_3 62 117 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 117 283 (Polychromatic418967fa.accept_15_1_12_13_1_944 61 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 283
  (Polychromatic418967fa.accept_18_6_9_13_1_3320 60 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 117 283 (accept_3_3 59 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 117 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 283 (accept_3_3 56 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 117 283 (accept_3_3 53 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 117 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 117 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 283 (accept_3_3 50 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 283 (Polychromatic418967fa.accept_27_22_9_13_1_7917 49 117 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 283
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 117 283 (accept_3_3 47 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 117 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 283 (accept_3_3 44 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 117 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 283 (accept_3_3 41 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 117 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 283 (accept_3_3 38 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 117 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 117 283 (accept_3_3 35 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 283 (Polychromatic418967fa.accept_15_3_12_13_1_2549 33 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 283 (accept_3_3 32 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 283 (Polychromatic418967fa.accept_15_1_12_13_1_944 31 117
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 117 283 (accept_3_3 29 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 117 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 283 (accept_3_3 26 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 117
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 283
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 283 (accept_3_3 23 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 283 (Polychromatic418967fa.accept_17_4_15_11_1_6465 21 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 283 (accept_3_3 20 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 283 (Polychromatic418967fa.accept_21_19_12_10_1_5385 19
  117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 283 (accept_3_3 17 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 283 (accept_3_3 14 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 283 (Polychromatic418967fa.accept_17_13_15_11_1_2936 13 117 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 283
  (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 283 (accept_3_3 11 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 283 (accept_3_3 8 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 283 (Polychromatic418967fa.accept_16_7_5_11_1_4777 7 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 283 (accept_3_3 5 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 283 (accept_3_3 2 117 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 117 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 283 (allA_of_3_1 116 116 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 283
  (allA_succ_of_accept 114 115 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 114 115 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 283 (accept_3_3 113 115 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 115 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 112 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 111 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 115 283 (accept_3_3 110 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 109 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 115 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 108 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 115 283 (accept_3_3 107 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 115 283 (Polychromatic418967fa.accept_13_2_11_10_1_1881 106
  115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 115 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 105 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 115 283 (accept_3_3 104 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 115 283 (Polychromatic418967fa.accept_13_12_11_10_1_2711 103 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 102 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 115 283 (accept_3_3 101 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 100 115
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 115 283
  (Polychromatic418967fa.accept_13_8_11_10_1_636 99 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 115 283 (accept_3_3 98 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 115 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 97 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 115 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 115 283 (accept_3_3 95 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 115 283 (Polychromatic418967fa.accept_13_3_11_10_1_2647 94 115 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 93 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 115 283 (accept_3_3 92 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 115 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 90 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 115 283 (accept_3_3 89 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 88 115
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 87 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 283 (accept_3_3 86 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 115 283 (Polychromatic418967fa.accept_19_9_1_17_1_3879 85 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 115 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 283 (accept_3_3 83 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 283
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 81 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 115 283 (accept_3_3 80 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 115 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 79 115 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 115 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 115 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 283 (accept_3_3 77 115 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 115 283
  (Polychromatic418967fa.accept_15_1_10_13_1_939 76 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 115 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 115 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 115 283 (accept_3_3 74 115 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408
  72 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 283 (accept_3_3 71
  115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 115 283
  (Polychromatic418967fa.accept_16_6_3_11_1_3751 70 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 115 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 115 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 283 (accept_3_3 68 115 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 115 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 67 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 115 283 (accept_3_3 65 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 115 283 (Polychromatic418967fa.accept_15_3_10_13_1_2605 63 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 283 (accept_3_3 62 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 61 115
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 115 283 (accept_3_3 59 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 115 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 58 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 115 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 283 (accept_3_3 56 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 283
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 54 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 115 283 (accept_3_3 53 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 115 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 52 115 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 115 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 283 (accept_3_3 50 115 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 283
  (Polychromatic418967fa.accept_15_4_10_13_1_2565 49 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 283 (accept_3_3 47 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 283
  (Polychromatic418967fa.accept_20_5_15_3_1_4516 45 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 283 (accept_3_3 44 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 43 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 283 (accept_3_3 41 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 283 (Polychromatic418967fa.accept_13_1_11_10_1_1258 40 115 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 283 (accept_3_3 38 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 283 (accept_3_3 35 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 283 (Polychromatic418967fa.accept_13_8_11_10_1_636 34 115
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 283 (accept_3_3 32 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 283 (accept_3_3 29 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 283
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 283 (accept_3_3 26 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 283 (accept_3_3 23 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 283 (accept_3_3 20 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 283 (accept_3_3 17 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 283 (Polychromatic418967fa.accept_13_3_11_10_1_2647 16 115
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 283 (accept_3_3 14 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 283 (accept_3_3 11 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 283
  (Polychromatic418967fa.accept_19_9_1_17_1_3879 9 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 283 (accept_3_3 8 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 283 (accept_3_3 5 115 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 115 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 283 (accept_3_3 2 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 115 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 283 (allA_succ_of_accept 113 114 283 (accept_3_3 113 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 114 283 (Polychromatic418967fa.accept_15_7_9_13_1_3451 112 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 114 283 (Polychromatic418967fa.accept_7_6_2_3_1_107
  111 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 283 (accept_3_3
  110 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 114 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 114 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 108 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 283 (accept_3_3 107 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 106 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 114 283 (accept_3_3 104 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 114 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 114 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 102 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 283 (accept_3_3 101 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 100 114
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 114 283 (accept_3_3 98 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 114 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 114 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 283 (accept_3_3 95 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 94 114 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 114 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 114 283 (accept_3_3 92 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 114 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 114 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 114 283 (accept_3_3 89 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 283
  (Polychromatic418967fa.accept_10_7_4_3_1_560 87 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 114 283 (accept_3_3 86 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 114 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 114 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 114 283 (accept_3_3 83 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 114 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 114 283 (accept_3_3 80 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 114 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 114 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 114 283 (accept_3_3 77 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 114 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 114 283 (accept_3_3 74 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 114 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 114 283 (Polychromatic418967fa.accept_23_3_22_7_1_2739 72 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 114 283 (accept_3_3 71 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 114 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 114 283 (accept_3_3 68 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 114 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 67 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 114 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 114 283 (accept_3_3 65 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 114 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 63 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 114 283 (accept_3_3 62 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 114 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 114 283 (Polychromatic418967fa.accept_21_18_9_10_1_2571 60 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 114 283 (accept_3_3 59 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 283 (Polychromatic418967fa.accept_21_16_9_10_1_14488 58
  114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 114 283 (accept_3_3 56 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 114 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 114 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 283 (accept_3_3 53 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 283
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 114 283 (accept_3_3 50 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 114 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 114 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 283 (accept_3_3 47 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 114 283 (accept_3_3 44 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 114 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 114 283 (Polychromatic418967fa.accept_25_17_14_8_1_15720 42 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 283 (accept_3_3 41 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 114 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 114 283 (accept_3_3 38 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 114 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 114 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 283 (accept_3_3 35 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 114 283 (accept_3_3 32 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 114 283 (Polychromatic418967fa.accept_17_14_12_11_1_4063 31 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 283 (accept_3_3 29 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 114 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 114 283 (accept_3_3 26 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 114 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 114 283 (Polychromatic418967fa.accept_20_4_14_3_1_3181 24 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 283 (accept_3_3 23 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 114 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 114 283 (accept_3_3 20 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 114 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 114 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 283 (accept_3_3 17 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 114 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 114 283 (accept_3_3 14 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 114 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 114 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 283 (accept_3_3 11 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 114 283 (accept_3_3 8 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  114 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 114 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 283 (accept_3_3 5 114 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 4 114 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 114 283 (accept_3_3 2 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  114 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 114
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 283 (allA_of_3_1 113 113 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 283
  (allA_succ_of_accept 111 112 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 112 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 112 283 (accept_3_3 110 112 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 112 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 109 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 112 283
  (Polychromatic418967fa.accept_13_4_8_10_1_671 108 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 112 283 (accept_3_3 107 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 112 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 106 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 112 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 112 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 112 283 (accept_3_3 104 112 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 112 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 103 112 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 112 283
  (Polychromatic418967fa.accept_13_11_8_10_1_676 102 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 112 283 (accept_3_3 101 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 112 283 (Polychromatic418967fa.accept_18_10_4_13_1_3296 100 112 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 112 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 99
  112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 112 283 (accept_3_3 98
  112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 112 283
  (Polychromatic418967fa.accept_18_7_4_13_1_3315 97 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 112 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 96 112 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 112 283 (accept_3_3 95 112 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 112 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 94 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 112 283 (accept_3_3 92 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 112 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 91 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 112 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 90 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 112 283 (accept_3_3 89 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 112 283 (Polychromatic418967fa.accept_17_3_10_11_1_7848 88 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 112 283 (accept_3_3 86 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 112 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 85 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 112 283 (Polychromatic418967fa.accept_15_9_7_13_1_1664 84 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 112 283 (accept_3_3 83 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 112 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 82 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 112 283 (accept_3_3 80 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 112 283 (Polychromatic418967fa.accept_18_7_4_13_1_3315 79 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 112 283 (Polychromatic418967fa.accept_21_15_7_10_1_8610 78 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 112 283 (accept_3_3 77 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 112 283 (Polychromatic418967fa.accept_13_11_8_10_1_676 76 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 112 283 (accept_3_3 74 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 112 283 (Polychromatic418967fa.accept_20_13_12_3_1_5972 73 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 112 283 (Polychromatic418967fa.accept_13_7_8_10_1_2663 72 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 112 283 (accept_3_3 71 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 112 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 112 283 (accept_3_3 68 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 112 283 (Polychromatic418967fa.accept_13_2_8_10_1_1902 67 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 112 283 (Polychromatic418967fa.accept_15_6_7_13_1_1666 66 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 283 (accept_3_3 65 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 112 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 64 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 112 283 (accept_3_3 62 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 112 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 61 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 112 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 283 (accept_3_3 59 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 112 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 283 (accept_3_3 56 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 55 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 283 (Polychromatic418967fa.accept_13_2_8_10_1_1902 54 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 283 (accept_3_3 53 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 283 (Polychromatic418967fa.accept_17_1_10_11_1_2943 52 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 283 (accept_3_3 50 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 283 (Polychromatic418967fa.accept_23_2_20_7_1_17354 48 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 283 (accept_3_3 47 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 283 (accept_3_3 44 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 283 (Polychromatic418967fa.accept_13_4_8_10_1_671 43 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 283 (Polychromatic418967fa.accept_22_20_2_19_1_14255 42 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 283 (accept_3_3 41 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 283 (Polychromatic418967fa.accept_21_19_7_10_1_7006 40 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 283 (accept_3_3 38 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 283 (Polychromatic418967fa.accept_13_11_8_10_1_676 37 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 283 (Polychromatic418967fa.accept_15_6_7_13_1_1666 36 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 283 (accept_3_3 35 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 283 (accept_3_3 32 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 283 (Polychromatic418967fa.accept_13_4_8_10_1_671 30 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 283 (accept_3_3 29 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 283 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 283 (accept_3_3 26 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 283 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 283 (accept_3_3 23 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 283 (accept_3_3 20 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 283 (Polychromatic418967fa.accept_21_19_7_10_1_7006 19 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 283 (accept_3_3 17 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 283 (accept_3_3 14 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 283 (Polychromatic418967fa.accept_20_13_12_3_1_5972 13 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 112 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 283 (accept_3_3 11 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 112
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 283 (accept_3_3 8 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 283 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 283 (Polychromatic418967fa.accept_15_6_7_13_1_1666 6 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 283 (accept_3_3 5 112 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 283 (Polychromatic418967fa.accept_13_4_8_10_1_671 4 112 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 283 (accept_3_3 2 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 112 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 283 (allA_succ_of_accept 110 111 283 (accept_3_3 110 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 109 111 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 108 111
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 283 (accept_3_3 107 111
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 106 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 111 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 105 111 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 283 (accept_3_3 104 111 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 111 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 103 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 102 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 111 283 (accept_3_3 101 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 111 283 (Polychromatic418967fa.accept_13_8_7_10_1_4362 99 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 283 (accept_3_3 98 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 97 111 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 96 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 111 283 (accept_3_3 95 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 111 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 283 (accept_3_3 92 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 283
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 90 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 111 283 (accept_3_3 89 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 111 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 111 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 111 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 283 (accept_3_3 86 111 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 283
  (Polychromatic418967fa.accept_23_16_19_7_1_17353 85 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 111 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 283 (accept_3_3 83 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 111 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 111 283 (accept_3_3 80 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 111 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 111 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 283 (accept_3_3 77 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 111 283
  (Polychromatic418967fa.accept_19_18_16_17_1_2626 75 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 283 (accept_3_3 74 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 111 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 111 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 111 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 283 (accept_3_3 71 111 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70
  111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 111 283 (accept_3_3 68 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 111 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 111 283 (Polychromatic418967fa.accept_14_10_13_3_1_2552 66 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 283 (accept_3_3 65 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 111 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 111 283
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 63 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 111 283 (accept_3_3 62 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 111 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 111 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 283 (accept_3_3 59 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 111 283 (accept_3_3 56 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 111 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 111 283 (Polychromatic418967fa.accept_17_3_9_11_1_11600 54 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 283 (accept_3_3 53 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 111 283 (accept_3_3 50 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 111 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 49 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 111 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 283 (accept_3_3 47 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 111 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 111 283 (accept_3_3 44 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 111 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 111 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 283 (accept_3_3 41 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 111 283 (accept_3_3 38 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 111 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 111 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 283 (accept_3_3 35 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 111 283 (accept_3_3 32 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 111 283 (Polychromatic418967fa.accept_23_8_19_7_1_11097 31 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 111 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 283 (accept_3_3 29 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 283
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 27 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 111 283 (accept_3_3 26 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 111 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 111 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 283 (accept_3_3 23 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 283 (accept_3_3 20 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 111 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 283 (accept_3_3 17 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 283 (accept_3_3 14 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 283 (Polychromatic418967fa.accept_19_13_16_17_1_5140 13 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 283 (accept_3_3 11 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 111 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 283 (accept_3_3 8 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 283 (accept_3_3 5 111 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 283
  (Polychromatic418967fa.accept_13_3_7_10_1_668 3 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 283 (accept_3_3 2 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 111 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 283 (allA_of_3_1 110 110 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 283
  (allA_succ_of_accept 108 109 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 108 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 283 (accept_3_3 107 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 105 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 283 (accept_3_3 104 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 283 (Polychromatic418967fa.accept_17_1_7_11_1_2892 103 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 283 (accept_3_3 101 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 100
  109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 99 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 283 (accept_3_3 98 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 283 (accept_3_3 95 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 93 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 283 (accept_3_3 92 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365 91 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 283 (accept_3_3 89 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 87 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 283 (accept_3_3 86 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 283 (accept_3_3 83 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 283
  (Polychromatic418967fa.accept_15_6_4_13_1_403 81 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 283 (accept_3_3 80 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 283 (accept_3_3 77 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 75 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 283 (accept_3_3 74 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 283 (Polychromatic418967fa.accept_13_8_5_10_1_2701 73 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 283 (Polychromatic418967fa.accept_16_8_13_11_1_4772 72 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 283 (accept_3_3 71 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 109 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 283 (accept_3_3 68 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 283 (Polychromatic418967fa.accept_13_2_5_10_1_250 67 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 283 (accept_3_3 65 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 283
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 283 (accept_3_3 62 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 283 (accept_3_3 59 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 283 (accept_3_3 56 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 283 (accept_3_3 53 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 51 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 283 (accept_3_3 50 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365 49 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 283 (accept_3_3 47 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 283
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 45 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 283 (accept_3_3 44 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 283 (accept_3_3 41 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 40 109 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 283 (accept_3_3 38 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 283 (Polychromatic418967fa.accept_21_16_4_10_1_14506 37 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 283 (accept_3_3 35 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 283 (accept_3_3 32 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 283 (accept_3_3 29 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 283 (Polychromatic418967fa.accept_13_2_5_10_1_250 28 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 283 (accept_3_3 26 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 283 (accept_3_3 23 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 283 (accept_3_3 20 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 283 (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 283 (accept_3_3 17 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 283 (accept_3_3 14 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 283 (accept_3_3 11 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 283
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 283 (accept_3_3 8 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 283 (accept_3_3 5 109 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 109 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 283 (accept_3_3 2 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 109 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 283 (allA_succ_of_accept 107 108 283 (accept_3_3 107 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 108 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 106 108 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 105 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 283 (accept_3_3 104 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 108 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 103 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 108 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 102 108 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 283 (accept_3_3 101 108 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 283 (Polychromatic418967fa.accept_15_10_3_13_1_4480 100 108 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 283
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 99 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 108 283 (accept_3_3 98 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 108 283 (Polychromatic418967fa.accept_13_6_4_10_1_660 97 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 108 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 96 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 108 283 (accept_3_3 95 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 283 (Polychromatic418967fa.accept_19_18_13_17_1_9517 94
  108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 283
  (Polychromatic418967fa.accept_20_13_8_3_1_11818 93 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 108 283 (accept_3_3 92 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 108 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 91 108 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 108 283 (Polychromatic418967fa.accept_14_6_10_3_1_1038 90 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 108 283 (accept_3_3 89 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 283
  (Polychromatic418967fa.accept_16_8_12_11_1_3697 88 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 108 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 87 108 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 108 283 (accept_3_3 86 108 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 108 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 85 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 108 283
  (Polychromatic418967fa.accept_13_6_4_10_1_660 84 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 108 283 (accept_3_3 83 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 108 283 (Polychromatic418967fa.accept_19_6_13_17_1_8015 82 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 108 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 81 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 108 283 (accept_3_3 80 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 108 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 108 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 108 283
  (Polychromatic418967fa.accept_20_18_8_3_1_9071 78 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 108 283 (accept_3_3 77 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 108 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 76 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 108 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 75 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 283 (accept_3_3 74 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 283 (Polychromatic418967fa.accept_13_8_4_10_1_4358 73 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 108 283
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 72 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 108 283 (accept_3_3 71 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 108 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 70 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 108 283 (Polychromatic418967fa.accept_14_13_10_3_1_1037 69 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 283 (accept_3_3 68 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 283 (Polychromatic418967fa.accept_22_1_20_19_1_17352 67
  108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 108 283
  (Polychromatic418967fa.accept_10_6_8_3_1_930 66 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 108 283 (accept_3_3 65 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 108 283 (Polychromatic418967fa.accept_17_13_6_11_1_4014 64 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 108 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 108 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 283 (accept_3_3 62 108 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 61 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 108 283
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 60 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 108 283 (accept_3_3 59 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 108 283 (Polychromatic418967fa.accept_13_6_4_10_1_660 58 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 108 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 57 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 283 (accept_3_3 56 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 108 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 283
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 108 283 (accept_3_3 53 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 108 283 (Polychromatic418967fa.accept_16_4_12_11_1_2650 52 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 108 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 283 (accept_3_3 50 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 283 (Polychromatic418967fa.accept_14_7_10_3_1_1034 49 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 283
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 108 283 (accept_3_3 47 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 108 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 108 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 283 (accept_3_3 44 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 283
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 42 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 108 283 (accept_3_3 41 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 108 283 (Polychromatic418967fa.accept_13_1_4_10_1_622 40 108 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 108 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 283 (accept_3_3 38 108 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 283
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 37 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 108 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 283 (accept_3_3 35 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 283 (Polychromatic418967fa.accept_13_8_4_10_1_4358 34 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 283
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 33 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 283 (accept_3_3 32 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 108 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 108 283 (Polychromatic418967fa.accept_17_13_6_11_1_4014 30 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 283 (accept_3_3 29 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 283 (Polychromatic418967fa.accept_19_9_13_17_1_9506 28 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 283
  (Polychromatic418967fa.accept_13_1_4_10_1_622 27 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 108 283 (accept_3_3 26 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 108 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 108 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 283 (accept_3_3 23 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 283 (Polychromatic418967fa.accept_17_5_6_11_1_3974 22 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 283
  (Polychromatic418967fa.accept_10_1_8_3_1_947 21 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 283 (accept_3_3 20 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 108 283 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 108 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 283 (accept_3_3 17 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 108 283 (accept_3_3 14 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 108 283 (Polychromatic418967fa.accept_14_13_10_3_1_1037 13 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 108 283 (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 283 (accept_3_3 11 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 108
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 283
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 108 283 (accept_3_3 8 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  108 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 108 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 108 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 283 (accept_3_3 5 108 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 283 (Polychromatic418967fa.accept_16_4_12_11_1_2650 4 108 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 283
  (Polychromatic418967fa.accept_22_3_20_19_1_17351 3 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 283 (accept_3_3 2 108 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 108 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 283 (allA_of_3_1 107 107 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 283
  (allA_succ_of_accept 105 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 106 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 283 (accept_3_3 104 106 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 106 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 103 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 102 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 106 283 (accept_3_3 101 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 106 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 106 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 283 (accept_3_3 98 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 96 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 283 (accept_3_3 95 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 283 (Polychromatic418967fa.accept_13_3_2_10_1_2697 94 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 283 (accept_3_3 92 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 283
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 90 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 106 283 (accept_3_3 89 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 106 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 106 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 106 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 106 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 283 (accept_3_3 86 106 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85
  106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 283 (accept_3_3 83 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 283 (accept_3_3 80 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 283 (accept_3_3 77 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 283 (accept_3_3 74 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 283 (accept_3_3 71 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 70 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 283 (accept_3_3 68 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 283 (accept_3_3 65 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 283 (accept_3_3 62 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 283 (accept_3_3 59 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 283 (accept_3_3 56 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 283 (accept_3_3 53 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 283 (accept_3_3 50 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 283 (accept_3_3 47 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 283 (accept_3_3 44 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 283 (Polychromatic418967fa.accept_19_5_11_17_1_6536 43 106 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 283 (accept_3_3 41 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 283 (accept_3_3 38 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 283
  (Polychromatic418967fa.accept_21_15_1_10_1_8592 36 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 106 283 (accept_3_3 35 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 106 283 (Polychromatic418967fa.accept_13_8_2_10_1_652 34 106 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 283 (accept_3_3 32 106 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 283 (Polychromatic418967fa.accept_13_5_2_10_1_248
  31 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 283 (accept_3_3 29 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 283 (accept_3_3 26 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 283 (accept_3_3 23 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 283 (Polychromatic418967fa.accept_27_22_25_13_1_17350 22 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 283 (accept_3_3 20 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 106 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 283 (accept_3_3 17 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 283 (accept_3_3 14 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 283 (accept_3_3 11 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 283 (accept_3_3 8 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 283 (accept_3_3 5 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 106 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 283 (accept_3_3 2 106 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 283 (allA_succ_of_accept 104 105 283 (accept_3_3 104 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 283 (Polychromatic418967fa.accept_19_8_10_17_1_12082 103 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 283 (Polychromatic418967fa.accept_4_2_1_3_1_27
  102 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 283 (accept_3_3
  101 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 100 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 99 105 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 283 (accept_3_3 98 105 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 105 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 97 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 283
  (Polychromatic418967fa.accept_19_1_10_17_1_5188 96 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 105 283 (accept_3_3 95 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 105 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 105 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 105 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 283 (accept_3_3 92 105 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 91
  105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 105 283 (accept_3_3 89 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 105 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 105 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 87 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 283 (accept_3_3 86 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 283 (Polychromatic418967fa.accept_16_5_9_11_1_3762 85 105
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 105 283 (accept_3_3 83 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 105 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 105 283 (Polychromatic418967fa.accept_14_11_7_3_1_3416 81 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 283 (accept_3_3 80 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 105 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 105 283 (accept_3_3 77 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 105 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 105 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 283 (accept_3_3 74 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 283
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 105 283 (accept_3_3 71 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 105 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 105 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 283 (accept_3_3 68 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 67 105
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 283 (accept_3_3 65 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 105 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 105 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 283 (accept_3_3 62 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 105 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 283
  (Polychromatic418967fa.accept_14_4_7_3_1_1718 60 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 105 283 (accept_3_3 59 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 105 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 283 (accept_3_3 56 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 283 (accept_3_3 53 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 51 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 283 (accept_3_3 50 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 283 (Polychromatic418967fa.accept_22_5_17_19_1_12866 49
  105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 283 (accept_3_3 47 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 283 (Polychromatic418967fa.accept_19_7_10_17_1_8088 45 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 283 (accept_3_3 44 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 105 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 283 (accept_3_3 41 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 283 (accept_3_3 38 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 283
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 283 (accept_3_3 35 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 283 (Polychromatic418967fa.accept_27_6_24_13_1_17349 33 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 283 (accept_3_3 32 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 283 (Polychromatic418967fa.accept_17_14_3_11_1_11591 31
  105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 283 (accept_3_3 29 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 283 (accept_3_3 26 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 105 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 283
  (Polychromatic418967fa.accept_13_11_1_10_1_648 24 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 283 (accept_3_3 23 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 283 (accept_3_3 20 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 283 (accept_3_3 17 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 15 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 283 (accept_3_3 14 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 283 (Polychromatic418967fa.accept_22_13_17_19_1_15950 13
  105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 283 (accept_3_3 11 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 283 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 283 (accept_3_3 8 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 283 (accept_3_3 5 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 283 (accept_3_3 2 105 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 105 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 283 (allA_of_3_1 104 104 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 283
  (allA_succ_of_accept 102 103 283 (Polychromatic418967fa.accept_13_11_12_10_1_2652 102 103 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 283 (accept_3_3 101 103 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 103 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 99 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 283 (accept_3_3 98 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 283 (Polychromatic418967fa.accept_13_6_12_10_1_690 97 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 283 (Polychromatic418967fa.accept_14_12_5_3_1_1011 96 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 283 (accept_3_3 95 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 283 (Polychromatic418967fa.accept_22_6_15_19_1_14254 94
  103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 283 (accept_3_3 92 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 283 (Polychromatic418967fa.accept_19_15_8_17_1_9429 91 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 283 (Polychromatic418967fa.accept_27_9_22_13_1_7932 90 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 283 (accept_3_3 89 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 283 (Polychromatic418967fa.accept_21_4_19_10_1_8531 88 103
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 283
  (Polychromatic418967fa.accept_13_9_12_10_1_242 87 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 283 (accept_3_3 86 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 103 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 283 (accept_3_3 83 103 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 283 (Polychromatic418967fa.accept_14_12_5_3_1_1011 82 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 283
  (Polychromatic418967fa.accept_26_3_25_23_1_11943 81 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 103 283 (accept_3_3 80 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 103 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 103 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 103 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 283 (accept_3_3 77 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 283 (Polychromatic418967fa.accept_8_4_7_3_1_144
  76 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 283
  (Polychromatic418967fa.accept_17_7_1_11_1_1894 75 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 283 (accept_3_3 74 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 73 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 103 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 283 (accept_3_3 71 103 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 283 (Polychromatic418967fa.accept_21_7_19_10_1_8567 70 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 283
  (Polychromatic418967fa.accept_16_5_7_11_1_2664 69 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 283 (accept_3_3 68 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 283 (Polychromatic418967fa.accept_16_2_7_11_1_1698 66 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 283 (accept_3_3 65 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 283
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 103 283 (accept_3_3 62 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 103 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 61 103 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 283 (accept_3_3 59 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 58
  103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 283 (accept_3_3 56 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 283 (Polychromatic418967fa.accept_23_9_11_7_1_17348 55 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 283 (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 283 (accept_3_3 53 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 283 (accept_3_3 50 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 283 (Polychromatic418967fa.accept_19_11_8_17_1_12103 49 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 48 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 283 (accept_3_3 47 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 283
  (Polychromatic418967fa.accept_13_7_12_10_1_640 46 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 103 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 103 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 283 (accept_3_3 44 103 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 103 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 103 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 283
  (Polychromatic418967fa.accept_17_8_1_11_1_4004 42 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 283 (accept_3_3 41 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 283 (Polychromatic418967fa.accept_23_16_11_7_1_15890 39 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 283 (accept_3_3 38 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 283 (accept_3_3 35 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 283 (Polychromatic418967fa.accept_13_7_12_10_1_640 33 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 283 (accept_3_3 32 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 283 (Polychromatic418967fa.accept_16_15_7_11_1_3760 31 103
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 283 (accept_3_3 29 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 283 (Polychromatic418967fa.accept_17_10_1_11_1_2900 27 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 283 (accept_3_3 26 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 283 (Polychromatic418967fa.accept_17_8_1_11_1_4004 25 103
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 283
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 103 283 (accept_3_3 23 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 103 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 103 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 283 (Polychromatic418967fa.accept_13_8_12_10_1_4414 21 103
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 283 (accept_3_3 20 103
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 283
  (Polychromatic418967fa.accept_13_6_12_10_1_690 19 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 103 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 103 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 283 (accept_3_3 17 103 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 103 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 103 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 283 (Polychromatic418967fa.accept_7_1_5_3_1_268
  15 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 283 (accept_3_3 14
  103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 283
  (Polychromatic418967fa.accept_24_13_7_19_1_10760 13 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 103 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 283 (accept_3_3 11 103 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 283 (Polychromatic418967fa.accept_17_10_1_11_1_2900 10 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 283 (accept_3_3 8 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 283 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 283 (accept_3_3 5 103 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 103 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 283
  (Polychromatic418967fa.accept_16_3_7_11_1_1723 3 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 283 (accept_3_3 2 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 103 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 283 (allA_succ_of_accept 101 102 283 (accept_3_3 101 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 102 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 100 102 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 102 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 99 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 283 (accept_3_3 98 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97
  102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 96 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 283 (accept_3_3 95 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 102 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 94 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 283 (accept_3_3 92 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 90 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 102 283 (accept_3_3 89 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 102 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 102 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 283 (accept_3_3 86 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 283
  (Polychromatic418967fa.accept_16_4_6_11_1_3753 84 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 102 283 (accept_3_3 83 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 102 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 283 (accept_3_3 80 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 78 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 102 283 (accept_3_3 77 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 102 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 102 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 75 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 283 (accept_3_3 74 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 283
  (Polychromatic418967fa.accept_11_6_3_8_1_843 72 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 102 283 (accept_3_3 71 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 102 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 283 (accept_3_3 68 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 283 (Polychromatic418967fa.accept_13_2_11_10_1_1881 67 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 283
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 66 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 102 283 (accept_3_3 65 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 102 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 102 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 102 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 63 102
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 283 (accept_3_3 62 102
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  61 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 283 (accept_3_3 59 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 102 283 (Polychromatic418967fa.accept_20_18_2_3_1_3169 58 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 283 (accept_3_3 56 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 283
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 54 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 283 (accept_3_3 53 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 102 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 102 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 283 (accept_3_3 50 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 102 283 (accept_3_3 47 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 102 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 283 (accept_3_3 44 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 283 (accept_3_3 41 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 283 (Polychromatic418967fa.accept_13_1_11_10_1_1258 40 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 39 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 283 (accept_3_3 38 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 102 283 (accept_3_3 35 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 102 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 283 (accept_3_3 32 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 283
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 30 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 283 (accept_3_3 29 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 102 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 283 (accept_3_3 26 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 283 (accept_3_3 23 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 283 (accept_3_3 20 102 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 283 (accept_3_3 17 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 102 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 283 (accept_3_3 14 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 283
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 283 (accept_3_3 11 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 102 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 283 (accept_3_3 8 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 283 (accept_3_3 5 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 102 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 283 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 283 (accept_3_3 2 102 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 283 (allA_of_3_1 101 101 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 283 (allA_succ_of_accept 99
  100 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 100 283 (accept_3_3 98 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 100 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 100 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 100 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 100 283 (accept_3_3 95 100 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 100 283 (Polychromatic418967fa.accept_12_10_4_7_1_948
  94 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 100 283 (accept_3_3 92 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 100 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 91 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 100 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 100 283 (accept_3_3 89 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 100 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 100 283 (accept_3_3 86 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 100 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 100 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 100 283 (accept_3_3 83 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 100 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 100 283 (accept_3_3 80 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 100 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 100 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 100 283 (accept_3_3 77 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 100 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 100 283 (accept_3_3 74 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 100 283 (Polychromatic418967fa.accept_16_9_4_11_1_2661 73 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 100 283 (Polychromatic418967fa.accept_15_12_10_13_1_4497 72 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 100 283 (accept_3_3 71 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 100 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 100 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 100 283 (accept_3_3 68 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 100 283 (Polychromatic418967fa.accept_17_16_15_11_1_10421 67 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 100 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 100 283 (accept_3_3 65 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 100 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 100 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 100 283 (accept_3_3 62 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 100 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 100 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 100 283 (accept_3_3 59 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 100 283 (accept_3_3 56 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 100 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 100 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 100 283 (accept_3_3 53 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 100 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 100 283 (accept_3_3 50 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 100 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 49 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 100 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 283 (accept_3_3 47 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 100 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 100 283 (accept_3_3 44 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 100 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 100 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 100 283 (accept_3_3 41 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 100 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 100 283 (accept_3_3 38 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 100 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 100 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 283 (accept_3_3 35 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 100 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 100 283 (accept_3_3 32 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 100 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 100 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 283 (accept_3_3 29 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 283 (Polychromatic418967fa.accept_16_12_4_11_1_3710 28 100 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 283 (accept_3_3 26 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 100 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 100 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 283 (accept_3_3 23 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 283 (accept_3_3 20 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 283 (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 283 (accept_3_3 17 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 100 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 283 (accept_3_3 14 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 283 (accept_3_3 11 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 283 (accept_3_3 8 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 283 (accept_3_3 5 100 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 100 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 283 (accept_3_3 2 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 100 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  283 (allA_succ_of_accept 98 99 283 (accept_3_3 98 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 283 (Polychromatic418967fa.accept_15_7_9_13_1_3451 97 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 283 (accept_3_3 95 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 283 (accept_3_3 92 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 283 (Polychromatic418967fa.accept_21_7_15_10_1_1368 91 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 90 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 283 (accept_3_3 89 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 99 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 283
  (Polychromatic418967fa.accept_16_7_3_11_1_3682 87 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 283 (accept_3_3 86 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 283 (Polychromatic418967fa.accept_13_7_8_10_1_2663 85 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 283 (accept_3_3 83 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 283 (accept_3_3 80 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 78 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 283 (accept_3_3 77 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 99 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 283 (accept_3_3 74 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 283 (Polychromatic418967fa.accept_24_1_3_19_1_9038 73 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 283 (accept_3_3 71 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 69 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 283 (accept_3_3 68 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 66 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 283 (accept_3_3 65 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 283
  (Polychromatic418967fa.accept_13_11_8_10_1_676 63 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 283 (accept_3_3 62 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 283 (accept_3_3 59 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 283 (accept_3_3 56 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 283 (Polychromatic418967fa.accept_16_7_3_11_1_3682 55 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 283 (accept_3_3 53 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 283 (accept_3_3 50 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 49 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 48 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 283 (accept_3_3 47 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 99 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 283 (accept_3_3 44 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 283 (Polychromatic418967fa.accept_13_4_8_10_1_671 43 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 283 (Polychromatic418967fa.accept_17_8_14_11_1_9101 42 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 283 (accept_3_3 41 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 283 (accept_3_3 38 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 283 (accept_3_3 35 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 283 (accept_3_3 32 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 283 (accept_3_3 29 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 283
  (Polychromatic418967fa.accept_19_8_4_17_1_9510 27 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 283 (accept_3_3 26 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 283 (accept_3_3 23 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 283 (accept_3_3 20 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 283 (accept_3_3 17 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 283
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 283 (accept_3_3 14 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 283 (Polychromatic418967fa.accept_19_13_4_17_1_5166 13 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 283 (accept_3_3 11 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 283 (accept_3_3 8 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  283 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 283 (accept_3_3 5 99 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 283 (accept_3_3 2 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  283 (Polychromatic418967fa.accept_19_1_4_17_1_5136 1 99 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  283 (allA_of_3_1 98 98 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 283 (allA_succ_of_accept 96 97 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 96 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 283 (accept_3_3 95 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 283 (accept_3_3 92 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 283 (accept_3_3 89 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 87 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 283 (accept_3_3 86 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 85 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 283 (accept_3_3 83 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 283 (accept_3_3 80 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 283 (accept_3_3 77 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 76 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 283 (accept_3_3 74 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 283 (accept_3_3 71 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 283 (accept_3_3 68 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 283 (accept_3_3 65 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 283 (Polychromatic418967fa.accept_16_15_1_11_1_3747 63 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 283 (accept_3_3 62 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 283 (Polychromatic418967fa.accept_13_9_6_10_1_666 61 97 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 283 (accept_3_3 59 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 283 (accept_3_3 56 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 283 (accept_3_3 53 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 283 (Polychromatic418967fa.accept_14_10_13_3_1_2552 52 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 283 (accept_3_3 50 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 283 (Polychromatic418967fa.accept_21_7_13_10_1_8604 49 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 283 (accept_3_3 47 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 283 (accept_3_3 44 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 283 (accept_3_3 41 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 283 (Polychromatic418967fa.accept_17_6_12_11_1_5231 40 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 283 (accept_3_3 38 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 283
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 283 (accept_3_3 35 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 283 (accept_3_3 32 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 283 (accept_3_3 29 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 283 (Polychromatic418967fa.accept_24_3_1_19_1_15818 27 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 283 (accept_3_3 26 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 97 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 283 (accept_3_3 23 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 283 (accept_3_3 20 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 283 (accept_3_3 17 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 283 (accept_3_3 14 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 283 (Polychromatic418967fa.accept_17_13_12_11_1_2947 13 97 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 283 (accept_3_3 11 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 283 (accept_3_3 8 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 283 (Polychromatic418967fa.accept_19_7_2_17_1_9426 7 97 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 283 (accept_3_3 5 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 97 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 97 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 283 (accept_3_3 2 97 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 97 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 283
  (allA_succ_of_accept 95 96 283 (accept_3_3 95 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  96 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 94 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 96 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 96 283 (accept_3_3 92 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 283
  (Polychromatic418967fa.accept_19_14_1_17_1_8063 90 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 96 283 (accept_3_3 89 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  96 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 96 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 87 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 283 (accept_3_3 86 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 283 (accept_3_3 83 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  96 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 283 (Polychromatic418967fa.accept_18_9_6_13_1_4499 81 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 283 (accept_3_3 80 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 96 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 78 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 96 283 (accept_3_3 77 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  96 283 (Polychromatic418967fa.accept_22_10_8_19_1_12892 76 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 96 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 283 (accept_3_3 74 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 283 (accept_3_3 71 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  96 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 69 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 283 (accept_3_3 68 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 67 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 283 (accept_3_3 65 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 283 (Polychromatic418967fa.accept_18_9_6_13_1_4499 63 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 283 (accept_3_3 62 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 96 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 283
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 60 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 283 (accept_3_3 59 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 283 (accept_3_3 56 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 283
  (Polychromatic418967fa.accept_13_2_5_10_1_250 54 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 283 (accept_3_3 53 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 283 (accept_3_3 50 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 49 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 283 (accept_3_3 47 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 283 (Polychromatic418967fa.accept_13_6_5_10_1_1213 45 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 283 (accept_3_3 44 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 96 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 283
  (Polychromatic418967fa.accept_19_4_1_17_1_8064 42 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 283 (accept_3_3 41 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 283 (Polychromatic418967fa.accept_21_19_12_10_1_5385 40 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 283 (accept_3_3 38 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 283 (accept_3_3 35 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 283 (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 283 (accept_3_3 32 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 283 (Polychromatic418967fa.accept_22_9_8_19_1_8114 31 96
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 283 (accept_3_3 29 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 283 (accept_3_3 26 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 283
  (Polychromatic418967fa.accept_21_3_12_10_1_3885 24 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 283 (accept_3_3 23 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 283 (accept_3_3 20 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 283
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 283 (accept_3_3 17 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 283 (accept_3_3 14 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 283 (Polychromatic418967fa.accept_20_13_16_3_1_4479 13 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 283 (accept_3_3 11 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 283 (accept_3_3 8 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 283
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 283 (accept_3_3 5 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  283 (Polychromatic418967fa.accept_13_4_5_10_1_1247 4 96 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 96 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 283 (accept_3_3 2 96 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 283
  (allA_of_3_1 95 95 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 283 (allA_succ_of_accept 93 94 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 94 283 (accept_3_3 92 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  94 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 91 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 94 283 (Polychromatic418967fa.accept_14_6_10_3_1_1038 90 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 283 (accept_3_3 89 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 94 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 94 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 94 283 (accept_3_3 86 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  94 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 94 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 84 94 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 283 (accept_3_3 83 94 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 283 (Polychromatic418967fa.accept_18_10_4_13_1_3296 82 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 283 (accept_3_3 80 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 79 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 283 (Polychromatic418967fa.accept_22_12_6_19_1_8159 78 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 283 (accept_3_3 77 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 94 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 283 (accept_3_3 74 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 283 (Polychromatic418967fa.accept_13_7_3_10_1_656 72 94 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 283 (accept_3_3 71 94 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 70 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 283 (accept_3_3 68 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 67 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 283 (Polychromatic418967fa.accept_15_6_4_13_1_403 66 94 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 283 (accept_3_3 65 94 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 283 (accept_3_3 62 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 283 (Polychromatic418967fa.accept_25_10_19_8_1_12163 60 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 283 (accept_3_3 59 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 58 94 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 283 (accept_3_3 56 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 283 (Polychromatic418967fa.accept_14_13_10_3_1_1037 55 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 283 (Polychromatic418967fa.accept_13_2_3_10_1_658 54 94 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 283 (accept_3_3 53 94 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 283 (accept_3_3 50 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 283 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 283 (accept_3_3 47 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 283 (Polychromatic418967fa.accept_13_7_3_10_1_656 46 94 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 283 (accept_3_3 44 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 283 (Polychromatic418967fa.accept_18_7_4_13_1_3315 43 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 283 (Polychromatic418967fa.accept_17_8_9_11_1_3976 42 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 283 (accept_3_3 41 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 94 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 283 (accept_3_3 38 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 94 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 283 (accept_3_3 35 94 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 283 (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 283 (accept_3_3 32 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 283 (Polychromatic418967fa.accept_19_12_18_17_1_8075 31 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 283 (Polychromatic418967fa.accept_19_11_18_17_1_6538 30 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 283 (accept_3_3 29 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 94 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 283 (accept_3_3 26 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 283 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 283 (accept_3_3 23 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 283 (Polychromatic418967fa.accept_30_22_4_13_1_17347 22 94
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 283 (accept_3_3 20 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 283 (Polychromatic418967fa.accept_23_18_2_7_1_9297 18 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 283 (accept_3_3 17 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 94 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 283 (accept_3_3 14 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 283 (Polychromatic418967fa.accept_19_12_18_17_1_8075 12 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 283 (accept_3_3 11 94 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 94
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 283 (accept_3_3 8 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  283 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 94 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 6 94 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 283 (accept_3_3 5 94 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 94 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 283 (accept_3_3 2 94 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 283
  (allA_succ_of_accept 92 93 283 (accept_3_3 92 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 283 (accept_3_3 89 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 283 (accept_3_3 86 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 84 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 283 (accept_3_3 83 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 93 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 283
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 81 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 283 (accept_3_3 80 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 79 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 283 (accept_3_3 77 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 283 (accept_3_3 74 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 283 (Polychromatic418967fa.accept_15_12_3_13_1_4481 72 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 283 (accept_3_3 71 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 283 (accept_3_3 68 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 283 (Polychromatic418967fa.accept_29_9_6_22_1_17346 67 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 283 (accept_3_3 65 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 283 (accept_3_3 62 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 283 (accept_3_3 59 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 283 (accept_3_3 56 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 283 (accept_3_3 53 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 283 (accept_3_3 50 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 283 (Polychromatic418967fa.accept_21_7_9_10_1_2573 49 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 283 (accept_3_3 47 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 283
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 283 (accept_3_3 44 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 283 (accept_3_3 41 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 283 (accept_3_3 38 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 283 (accept_3_3 35 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 283 (accept_3_3 32 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 283 (Polychromatic418967fa.accept_13_5_2_10_1_248 31 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 283 (accept_3_3 29 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 283 (accept_3_3 26 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 283 (accept_3_3 23 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 283
  (Polychromatic418967fa.accept_13_8_2_10_1_652 21 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 283 (accept_3_3 20 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 283 (accept_3_3 17 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 283 (accept_3_3 14 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 283 (accept_3_3 11 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 283
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 283 (accept_3_3 8 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 283 (accept_3_3 5 93 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 3
  93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 283 (accept_3_3 2 93 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  93 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 283
  (allA_of_3_1 92 92 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 283 (allA_succ_of_accept 90 91 283
  (Polychromatic418967fa.accept_17_5_6_11_1_3974 90 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 283 (accept_3_3 89 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 87 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 283 (accept_3_3 86 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 85 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 91 283 (accept_3_3 83 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 82 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 283 (Polychromatic418967fa.accept_14_11_7_3_1_3416 81 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 283 (accept_3_3 80 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 91 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 78 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 91 283 (accept_3_3 77 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 283 (Polychromatic418967fa.accept_21_13_7_10_1_8599 76 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 283 (accept_3_3 74 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 283 (Polychromatic418967fa.accept_17_5_6_11_1_3974 73 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 283
  (Polychromatic418967fa.accept_10_2_1_3_1_233 72 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 283 (accept_3_3 71 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 283 (accept_3_3 68 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 283 (Polychromatic418967fa.accept_14_11_7_3_1_3416 67 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 283 (accept_3_3 65 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 283 (Polychromatic418967fa.accept_17_13_6_11_1_4014 64 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 283 (Polychromatic418967fa.accept_15_3_1_13_1_1672 63 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 283 (accept_3_3 62 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 91 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 283 (accept_3_3 59 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 58 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 283 (accept_3_3 56 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 55 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 283
  (Polychromatic418967fa.accept_20_14_11_3_1_9060 54 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 283 (accept_3_3 53 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 283 (accept_3_3 50 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 283 (accept_3_3 47 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 283 (Polychromatic418967fa.accept_14_4_7_3_1_1718 46 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 283 (Polychromatic418967fa.accept_19_7_15_17_1_5198 45 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 283 (accept_3_3 44 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 91 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 283 (accept_3_3 41 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 283 (accept_3_3 38 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 283 (Polychromatic418967fa.accept_21_16_7_10_1_8601 37 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 283
  (Polychromatic418967fa.accept_21_15_7_10_1_8610 36 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 283 (accept_3_3 35 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 283 (accept_3_3 32 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 283 (Polychromatic418967fa.accept_19_12_15_17_1_3837 31 91 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 283 (accept_3_3 29 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 283 (accept_3_3 26 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 283 (accept_3_3 23 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 22 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 283 (accept_3_3 20 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 283 (Polychromatic418967fa.accept_21_19_7_10_1_7006 19 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 283
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 283 (accept_3_3 17 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 283 (accept_3_3 14 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 283 (Polychromatic418967fa.accept_17_13_6_11_1_4014 13 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 283 (accept_3_3 11 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 283 (Polychromatic418967fa.accept_14_10_7_3_1_1022 10 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 283 (Polychromatic418967fa.accept_21_9_7_10_1_3907 9 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 283 (accept_3_3 8 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 283 (accept_3_3 5 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  283 (Polychromatic418967fa.accept_14_4_7_3_1_1718 4 91 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 283 (accept_3_3 2 91 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 283 (Polychromatic418967fa.accept_19_1_15_17_1_701 1 91 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 283
  (allA_succ_of_accept 89 90 283 (accept_3_3 89 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  90 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 87 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 283 (accept_3_3 86 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 90 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 283
  (Polychromatic418967fa.accept_13_6_12_10_1_690 84 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 283 (accept_3_3 83 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  90 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 82 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 90 283 (accept_3_3 80 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 283
  (Polychromatic418967fa.accept_19_2_14_17_1_700 78 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 90 283 (accept_3_3 77 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  90 283 (Polychromatic418967fa.accept_13_11_12_10_1_2652 76 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 90 283 (Polychromatic418967fa.accept_17_7_5_11_1_2922 75 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 283 (accept_3_3 74 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 90 283 (accept_3_3 71 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  90 283 (Polychromatic418967fa.accept_25_20_15_8_1_17345 70 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 283 (accept_3_3 68 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 283
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 66 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 90 283 (accept_3_3 65 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  90 283 (Polychromatic418967fa.accept_22_20_2_19_1_14255 64 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 90 283 (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 283 (accept_3_3 62 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 90 283 (accept_3_3 59 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  90 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 283 (accept_3_3 56 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 283 (Polychromatic418967fa.accept_20_15_10_3_1_7465 55 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 283
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 90 283 (accept_3_3 53 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  90 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 90 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 283 (accept_3_3 50 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 283
  (Polychromatic418967fa.accept_13_9_12_10_1_242 48 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 90 283 (accept_3_3 47 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  90 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 283 (accept_3_3 44 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 283 (Polychromatic418967fa.accept_19_5_14_17_1_6550 43 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 283
  (Polychromatic418967fa.accept_20_2_10_3_1_9059 42 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 90 283 (accept_3_3 41 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  90 283 (Polychromatic418967fa.accept_17_6_5_11_1_4073 40 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 90 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 283 (accept_3_3 38 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 283
  (Polychromatic418967fa.accept_21_15_6_10_1_10016 36 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 90 283 (accept_3_3 35 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 90 283 (Polychromatic418967fa.accept_13_8_12_10_1_4414 34 90 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 283 (accept_3_3 32 90 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 283
  (Polychromatic418967fa.accept_16_15_10_11_1_1727 31 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 90 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 283 (accept_3_3 29 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 283 (Polychromatic418967fa.accept_13_2_12_10_1_2649 28 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 283
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 90 283 (accept_3_3 26 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 90 283 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 283 (accept_3_3 23 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 22 90
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 90 283 (accept_3_3 20 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  90 283 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 90 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 283 (accept_3_3 17 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 283
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 90 283 (accept_3_3 14 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  90 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 90 283 (Polychromatic418967fa.accept_16_12_10_11_1_2667 12 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 283 (accept_3_3 11 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 90
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 283 (accept_3_3 8 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90
  283 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 90 283 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 283 (accept_3_3 5 90 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 90 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 283
  (Polychromatic418967fa.accept_19_3_14_17_1_6603 3 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 283 (accept_3_3 2 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90
  283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 283 (allA_of_3_1 89 89 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 283 (allA_succ_of_accept 87 88
  283 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 88 283 (accept_3_3 86 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  88 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 88 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 283 (accept_3_3 83 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 88 283 (accept_3_3 80 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  88 283 (Polychromatic418967fa.accept_19_3_12_17_1_6585 79 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 88 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 283 (accept_3_3 77 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 283 (accept_3_3 74 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 283 (Polychromatic418967fa.accept_19_15_12_17_1_5195 72 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 283 (accept_3_3 71 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 88 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 283 (accept_3_3 68 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 283 (Polychromatic418967fa.accept_16_3_8_11_1_2714 67 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 88 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 283 (accept_3_3 65 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 88 283 (accept_3_3 62 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  88 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 61 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 88 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 283 (accept_3_3 59 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 283 (accept_3_3 56 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 283 (Polychromatic418967fa.accept_20_14_8_3_1_6011 54 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 283 (accept_3_3 53 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 283 (Polychromatic418967fa.accept_16_4_8_11_1_5961 52 88
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 283 (accept_3_3 50 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 49 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 283 (accept_3_3 47 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 283 (accept_3_3 44 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 283 (accept_3_3 41 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 283 (Polychromatic418967fa.accept_19_2_12_17_1_5197 40 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 283 (accept_3_3 38 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 283 (accept_3_3 35 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 283 (accept_3_3 32 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 283 (accept_3_3 29 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 283 (accept_3_3 26 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 283 (accept_3_3 23 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 283 (accept_3_3 20 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 283 (Polychromatic418967fa.accept_19_18_12_17_1_8026 18 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 283 (accept_3_3 17 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 88 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 283 (accept_3_3 14 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 283 (accept_3_3 11 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 88 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 283 (accept_3_3 8 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  283 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 88 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 88 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 88 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 283 (accept_3_3 5 88 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 88 283 (Polychromatic418967fa.accept_16_4_8_11_1_5961 4 88 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 283 (accept_3_3 2 88 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 88
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 283
  (allA_succ_of_accept 86 87 283 (accept_3_3 86 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  87 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 85 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 283 (accept_3_3 83 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 283 (accept_3_3 80 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 283 (Polychromatic418967fa.accept_15_3_12_13_1_2549 78 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 283 (accept_3_3 77 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 283 (accept_3_3 74 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 283 (Polychromatic418967fa.accept_21_9_3_10_1_8573 72 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 283 (accept_3_3 71 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 87 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 69 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 283 (accept_3_3 68 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 283 (Polychromatic418967fa.accept_16_3_7_11_1_1723 67 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 283 (accept_3_3 65 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 63 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 283 (accept_3_3 62 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 283 (accept_3_3 59 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 283 (accept_3_3 56 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 283 (accept_3_3 53 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 283
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 51 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 283 (accept_3_3 50 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 283 (Polychromatic418967fa.accept_21_7_3_10_1_13044 49 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 283 (accept_3_3 47 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 283
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 283 (accept_3_3 44 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 283 (accept_3_3 41 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 283 (accept_3_3 38 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 283 (accept_3_3 35 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 283 (accept_3_3 32 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 283 (accept_3_3 29 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 283
  (Polychromatic418967fa.accept_13_1_9_10_1_625 27 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 283 (accept_3_3 26 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 283 (accept_3_3 23 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 283 (accept_3_3 20 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 283 (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 283 (accept_3_3 17 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 283
  (Polychromatic418967fa.accept_10_5_7_3_1_561 15 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 283 (accept_3_3 14 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 283 (Polychromatic418967fa.accept_19_13_11_17_1_5152 13 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 283 (accept_3_3 11 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 87 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 283
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 283 (accept_3_3 8 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 87 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 283 (accept_3_3 5 87 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  87 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 283 (accept_3_3 2 87 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 87
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 283
  (allA_of_3_1 86 86 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 283 (allA_succ_of_accept 84 85 283
  (Polychromatic418967fa.accept_19_8_9_17_1_5151 84 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 283 (accept_3_3 83 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 283 (accept_3_3 80 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 283 (accept_3_3 77 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 76 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 283 (accept_3_3 74 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 283 (Polychromatic418967fa.accept_13_8_7_10_1_4362 73 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 283 (accept_3_3 71 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 283 (Polychromatic418967fa.accept_13_4_7_10_1_1200 69 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 283 (accept_3_3 68 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 85 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 283 (accept_3_3 65 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 283 (Polychromatic418967fa.accept_13_12_7_10_1_2662 64 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 283 (Polychromatic418967fa.accept_15_3_10_13_1_2605 63 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 283 (accept_3_3 62 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 85 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 283 (accept_3_3 59 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 283 (accept_3_3 56 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 283 (Polychromatic418967fa.accept_13_3_7_10_1_668 55 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 283 (accept_3_3 53 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 52 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 283 (accept_3_3 50 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 49 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 283
  (Polychromatic418967fa.accept_10_8_5_3_1_543 48 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 283 (accept_3_3 47 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 283 (Polychromatic418967fa.accept_19_7_9_17_1_2638 45 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 283 (accept_3_3 44 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 283 (Polychromatic418967fa.accept_13_4_7_10_1_1200 43 85
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 283 (accept_3_3 41 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 283 (accept_3_3 38 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 283
  (Polychromatic418967fa.accept_21_15_1_10_1_8592 36 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 283 (accept_3_3 35 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 283 (accept_3_3 32 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 283 (accept_3_3 29 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 283 (accept_3_3 26 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 283
  (Polychromatic418967fa.accept_16_8_5_11_1_4776 24 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 283 (accept_3_3 23 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 283 (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 283 (accept_3_3 20 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 85 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 283 (accept_3_3 17 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 283 (Polychromatic418967fa.accept_20_15_5_3_1_1953 15 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 283 (accept_3_3 14 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 283 (Polychromatic418967fa.accept_19_13_9_17_1_8070 13 85
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 283 (accept_3_3 11 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 283 (accept_3_3 8 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 85 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 283 (accept_3_3 5 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 85 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 283 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 85 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 283 (accept_3_3 2 85 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 85 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 283
  (allA_succ_of_accept 83 84 283 (accept_3_3 83 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 81 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 283 (accept_3_3 80 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 84 283 (accept_3_3 77 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  84 283 (Polychromatic418967fa.accept_16_12_4_11_1_3710 76 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 84 283 (Polychromatic418967fa.accept_18_3_12_13_1_3307 75 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 283 (accept_3_3 74 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 84 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 283
  (Polychromatic418967fa.accept_16_8_4_11_1_2687 72 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 283 (accept_3_3 71 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 283 (accept_3_3 68 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 67 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 283
  (Polychromatic418967fa.accept_17_15_16_11_1_4001 66 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 84 283 (accept_3_3 65 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 84 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 84 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 84 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 283 (accept_3_3 62 84 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 61
  84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 283 (accept_3_3 59 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 283 (Polychromatic418967fa.accept_31_27_22_4_1_17344 58 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 283 (accept_3_3 56 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 283
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 283 (accept_3_3 53 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  84 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 283 (accept_3_3 50 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 283
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 283 (accept_3_3 47 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 283 (Polychromatic418967fa.accept_22_1_18_19_1_3294 45 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 283 (accept_3_3 44 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 84 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 283 (accept_3_3 41 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 283 (Polychromatic418967fa.accept_16_8_4_11_1_2687 40 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 283 (accept_3_3 38 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 283
  (Polychromatic418967fa.accept_23_13_15_7_1_17343 36 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 84 283 (accept_3_3 35 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 84 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 84 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 283 (accept_3_3 32 84 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31
  84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 283
  (Polychromatic418967fa.accept_13_4_6_10_1_1199 30 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 283 (accept_3_3 29 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 283 (accept_3_3 26 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 283 (accept_3_3 23 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 283 (Polychromatic418967fa.accept_13_9_6_10_1_666 22 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 283 (Polychromatic418967fa.accept_18_3_12_13_1_3307 21 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 283 (accept_3_3 20 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 283
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 283 (accept_3_3 17 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 283 (accept_3_3 14 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 283 (Polychromatic418967fa.accept_20_13_4_3_1_14612 13 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 283
  (Polychromatic418967fa.accept_13_12_6_10_1_667 12 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 283 (accept_3_3 11 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 283 (accept_3_3 8 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 283 (accept_3_3 5 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 84 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 84 283 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 283 (accept_3_3 2 84 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 283 (allA_of_3_1
  83 83 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 283 (allA_succ_of_accept 81 82 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 283 (accept_3_3 80 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 283 (accept_3_3 77 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 283 (accept_3_3 74 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 283 (accept_3_3 71 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 283 (accept_3_3 68 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 283 (Polychromatic418967fa.accept_17_16_14_11_1_7836 67 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 283 (accept_3_3 65 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 283 (accept_3_3 62 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 283 (accept_3_3 59 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 283 (accept_3_3 56 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 55 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 283 (Polychromatic418967fa.accept_15_9_7_13_1_1664 54 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 283 (accept_3_3 53 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 82 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 283 (accept_3_3 50 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 283 (accept_3_3 47 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 46 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 283 (accept_3_3 44 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 283 (accept_3_3 41 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 283 (accept_3_3 38 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 283 (accept_3_3 35 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 283 (accept_3_3 32 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 283 (accept_3_3 29 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 283 (accept_3_3 26 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 283 (accept_3_3 23 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 283 (accept_3_3 20 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 283 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 283 (accept_3_3 17 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 82 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 283 (accept_3_3 14 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 283 (accept_3_3 11 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 283 (Polychromatic418967fa.accept_20_10_2_3_1_7425 10 82 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 283 (accept_3_3 8 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 82 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 283 (accept_3_3 5 82 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 82 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 283 (accept_3_3 2 82 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 283
  (allA_succ_of_accept 80 81 283 (accept_3_3 80 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 79 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 283 (accept_3_3 77 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 75 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 283 (accept_3_3 74 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 73 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 283 (accept_3_3 71 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 283 (accept_3_3 68 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 283 (accept_3_3 65 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 283 (accept_3_3 62 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 283 (Polychromatic418967fa.accept_28_5_25_3_1_17342 61 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 283 (Polychromatic418967fa.accept_16_12_1_11_1_5958 60 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 283 (accept_3_3 59 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 283 (accept_3_3 56 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 283 (accept_3_3 53 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 283
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 283 (accept_3_3 50 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365 49 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 283 (accept_3_3 47 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 283
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 283 (accept_3_3 44 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 283 (accept_3_3 41 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 283 (accept_3_3 38 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 283 (Polychromatic418967fa.accept_13_11_3_10_1_4374 37 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 283 (accept_3_3 35 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 283
  (Polychromatic418967fa.accept_13_7_3_10_1_656 33 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 283 (accept_3_3 32 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 283 (Polychromatic418967fa.accept_16_15_1_11_1_3747 31 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 283 (accept_3_3 29 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 283 (accept_3_3 26 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 283 (Polychromatic418967fa.accept_20_5_1_3_1_5983 25 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 283 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 283 (accept_3_3 23 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 283
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 21 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 283 (accept_3_3 20 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 19 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 283 (accept_3_3 17 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 283 (accept_3_3 14 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 283 (accept_3_3 11 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 283
  (Polychromatic418967fa.accept_21_9_18_10_1_5388 9 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 283 (accept_3_3 8 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 283 (accept_3_3 5 81 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 283 (accept_3_3 2 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 81 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 283
  (allA_of_3_1 80 80 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 283 (allA_succ_of_accept 78 79 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 78 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 283 (accept_3_3 77 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 283 (accept_3_3 74 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 283
  (Polychromatic418967fa.accept_19_15_3_17_1_9451 72 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 283 (accept_3_3 71 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 70 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 283 (accept_3_3 68 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 283 (Polychromatic418967fa.accept_16_3_15_11_1_2676 67 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 283 (accept_3_3 65 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 283 (Polychromatic418967fa.accept_13_11_1_10_1_648 63 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 283 (accept_3_3 62 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 79 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 60 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 283 (accept_3_3 59 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 283 (Polychromatic418967fa.accept_16_10_15_11_1_3785 58 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 283 (accept_3_3 56 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 283 (accept_3_3 53 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 283 (accept_3_3 50 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 283 (accept_3_3 47 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 283 (Polychromatic418967fa.accept_21_3_16_10_1_3911 45 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 283 (accept_3_3 44 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 79 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 283 (accept_3_3 41 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 283 (accept_3_3 38 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 283 (accept_3_3 35 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 283 (accept_3_3 32 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 283 (Polychromatic418967fa.accept_19_12_3_17_1_5182 31 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 283 (accept_3_3 29 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 283 (accept_3_3 26 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 283 (accept_3_3 23 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 283 (accept_3_3 20 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 283
  (Polychromatic418967fa.accept_25_18_4_8_1_17341 18 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 283 (accept_3_3 17 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 283 (accept_3_3 14 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 283 (accept_3_3 11 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 283 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 283 (accept_3_3 8 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 283 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 79 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 283 (accept_3_3 5 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  283 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 79 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 79 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 283 (accept_3_3 2 79 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 79 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 283
  (allA_succ_of_accept 77 78 283 (accept_3_3 77 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 76 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 283 (accept_3_3 74 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 283 (accept_3_3 71 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 283 (accept_3_3 68 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 283 (accept_3_3 65 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 283 (Polychromatic418967fa.accept_18_9_6_13_1_4499 63 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 283 (accept_3_3 62 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 283 (accept_3_3 59 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 283 (accept_3_3 56 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 283 (accept_3_3 53 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 283 (accept_3_3 50 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 283 (accept_3_3 47 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 283 (accept_3_3 44 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 283
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 42 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 283 (accept_3_3 41 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 283 (accept_3_3 38 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 283
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 283 (accept_3_3 35 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 283 (accept_3_3 32 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 283 (accept_3_3 29 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 283 (Polychromatic418967fa.accept_15_12_3_13_1_4481 27 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 283 (accept_3_3 26 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 283
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 283 (accept_3_3 23 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 283 (Polychromatic418967fa.accept_19_3_2_17_1_6574 22 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 283 (accept_3_3 20 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 283 (accept_3_3 17 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 283 (accept_3_3 14 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 283 (accept_3_3 11 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 283 (accept_3_3 8 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 283
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 283 (accept_3_3 5 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 78 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 78 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 283 (accept_3_3 2 78 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 283 (allA_of_3_1 77 77
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 283 (allA_succ_of_accept 75 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 283 (accept_3_3 74 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 283 (Polychromatic418967fa.accept_13_8_11_10_1_636 73 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 283 (accept_3_3 71 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 283 (accept_3_3 68 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 283 (Polychromatic418967fa.accept_13_1_11_10_1_1258 66 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 283 (accept_3_3 65 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 64 76 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 283 (accept_3_3 62 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 283 (Polychromatic418967fa.accept_18_7_4_13_1_3315 61 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 283 (accept_3_3 59 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 283 (accept_3_3 56 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 283 (Polychromatic418967fa.accept_13_2_11_10_1_1881 54 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 283 (accept_3_3 53 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 76
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 283 (accept_3_3 50 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 49 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 283 (accept_3_3 47 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 283 (accept_3_3 44 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 43 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 283 (accept_3_3 41 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 283 (Polychromatic418967fa.accept_13_1_11_10_1_1258 40 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 283 (accept_3_3 38 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 283 (Polychromatic418967fa.accept_16_4_12_11_1_2650 36 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 283 (accept_3_3 35 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 76 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 283 (accept_3_3 32 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 283 (accept_3_3 29 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 283 (accept_3_3 26 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 283 (accept_3_3 23 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 76 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 283 (accept_3_3 20 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 283 (accept_3_3 17 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 283 (accept_3_3 14 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 283 (Polychromatic418967fa.accept_20_13_16_3_1_4479 13 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 283 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 283 (accept_3_3 11 76 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 76 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 283 (accept_3_3 8 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 283 (Polychromatic418967fa.accept_25_6_1_8_1_17340 6 76 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 283 (accept_3_3 5 76 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 76 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 283 (accept_3_3 2 76 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 283 (Polychromatic418967fa.accept_13_1_11_10_1_1258
  1 76 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 283 (allA_succ_of_accept
  74 75 283 (accept_3_3 74 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 283
  (Polychromatic418967fa.accept_9_1_3_4_1_47 73 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 75 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 283 (accept_3_3 71 75 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 69
  75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 283 (accept_3_3 68 75
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 283
  (Polychromatic418967fa.accept_10_7_5_3_1_542 67 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 75 283 (Polychromatic418967fa.accept_18_12_3_13_1_4494 66 75 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 283 (accept_3_3 65 75 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 75 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 283 (Polychromatic418967fa.accept_18_9_3_13_1_5905
  63 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 283 (accept_3_3 62
  75 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 61 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 75 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 75 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 283 (accept_3_3 59 75 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 57
  75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 283 (accept_3_3 56 75
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 283 (Polychromatic418967fa.accept_9_1_3_4_1_47
  55 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 283
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 283 (accept_3_3 53 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 283 (accept_3_3 50 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 283 (Polychromatic418967fa.accept_19_11_18_17_1_6538 49 75 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 283
  (Polychromatic418967fa.accept_10_8_5_3_1_543 48 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 283 (accept_3_3 47 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 45 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 283 (accept_3_3 44 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 75 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 283 (accept_3_3 41 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 283 (Polychromatic418967fa.accept_17_5_7_11_1_5274 39 75 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 283 (accept_3_3 38 75 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 75 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 283 (accept_3_3 35 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 283 (accept_3_3 32 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 283 (Polychromatic418967fa.accept_19_12_18_17_1_8075 31 75 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 283 (accept_3_3 29 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 283 (accept_3_3 26 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 75 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 283 (accept_3_3 23 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 75 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 283 (accept_3_3 20 75 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 75 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 283
  (Polychromatic418967fa.accept_10_8_5_3_1_543 18 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 283 (accept_3_3 17 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 283 (accept_3_3 14 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 283 (Polychromatic418967fa.accept_17_13_7_11_1_3985 13 75 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 283
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 283 (accept_3_3 11 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 283 (accept_3_3 8 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 75 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 283 (accept_3_3 5 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 283 (Polychromatic418967fa.accept_21_3_12_10_1_3885 3 75 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 283 (accept_3_3 2 75 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 75 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 283 (allA_of_3_1 74 74
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 283 (allA_succ_of_accept 72 73 283
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 72 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 283 (accept_3_3 71 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 283 (accept_3_3 68 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 283 (Polychromatic418967fa.accept_13_2_8_10_1_1902 67 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 283 (accept_3_3 65 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 64 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 283 (Polychromatic418967fa.accept_13_11_8_10_1_676 63 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 283 (accept_3_3 62 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 73 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 283 (accept_3_3 59 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 283 (accept_3_3 56 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 283 (Polychromatic418967fa.accept_24_7_1_19_1_2203 55 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 283 (accept_3_3 53 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 283 (accept_3_3 50 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 283 (Polychromatic418967fa.accept_17_15_5_11_1_6468 49 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 283 (accept_3_3 47 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 283 (Polychromatic418967fa.accept_19_7_16_17_1_6567 45 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 283 (accept_3_3 44 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 73 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 283 (accept_3_3 41 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 283 (Polychromatic418967fa.accept_17_6_5_11_1_4073 40 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 283 (accept_3_3 38 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 283
  (Polychromatic418967fa.accept_16_4_9_11_1_7159 36 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 283 (accept_3_3 35 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 283 (accept_3_3 32 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 283 (accept_3_3 29 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 283 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 283 (Polychromatic418967fa.accept_19_8_16_17_1_6552 27 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 283 (accept_3_3 26 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 73 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 283 (accept_3_3 23 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 283 (accept_3_3 20 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 283 (Polychromatic418967fa.accept_28_19_17_3_1_17339 19 73 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 283 (accept_3_3 17 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 283 (accept_3_3 14 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 283 (Polychromatic418967fa.accept_19_13_16_17_1_5140 13 73 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 283 (accept_3_3 11 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 283 (Polychromatic418967fa.accept_24_9_1_19_1_941 9 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 283 (accept_3_3 8 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 283 (accept_3_3 5 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 73 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 283 (accept_3_3 2 73 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 283 (Polychromatic418967fa.accept_19_1_16_17_1_3864 1 73 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 283 (allA_succ_of_accept 71
  72 283 (accept_3_3 71 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 283
  (Polychromatic418967fa.accept_15_10_12_13_1_2585 70 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 72 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 283 (accept_3_3 68 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 283 (Polychromatic418967fa.accept_16_3_8_11_1_2714 67 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 283
  (Polychromatic418967fa.accept_17_15_4_11_1_6515 66 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 72 283 (accept_3_3 65 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  72 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 72 283 (Polychromatic418967fa.accept_15_3_12_13_1_2549 63 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 283 (accept_3_3 62 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 72 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 283
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 60 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 283 (accept_3_3 59 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  72 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 58 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 283 (accept_3_3 56 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 72 283 (accept_3_3 53 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  72 283 (Polychromatic418967fa.accept_16_4_8_11_1_5961 52 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 283 (accept_3_3 50 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 283 (Polychromatic418967fa.accept_17_15_4_11_1_6515 49 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 283 (accept_3_3 47 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 283 (Polychromatic418967fa.accept_15_1_12_13_1_944 46 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 283 (accept_3_3 44 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 283
  (Polychromatic418967fa.accept_13_3_7_10_1_668 42 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 283 (accept_3_3 41 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 283 (Polychromatic418967fa.accept_19_1_15_17_1_701 39 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 283 (accept_3_3 38 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 283 (Polychromatic418967fa.accept_16_5_8_11_1_9582 37 72
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 283 (accept_3_3 35 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 283 (accept_3_3 32 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 283
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 30 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 283 (accept_3_3 29 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 283 (Polychromatic418967fa.accept_16_12_8_11_1_2695 28 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 283 (accept_3_3 26 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 283
  (Polychromatic418967fa.accept_19_5_15_17_1_9432 24 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 283 (accept_3_3 23 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 283 (accept_3_3 20 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 283 (accept_3_3 17 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 283 (Polychromatic418967fa.accept_13_3_7_10_1_668 16 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 283 (accept_3_3 14 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 283 (accept_3_3 11 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 283 (Polychromatic418967fa.accept_15_10_12_13_1_2585 10 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 283 (Polychromatic418967fa.accept_20_9_12_3_1_3191 9 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 283 (accept_3_3 8 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 283 (Polychromatic418967fa.accept_19_7_15_17_1_5198 7 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 283 (accept_3_3 5 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  283 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 72 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 283 (accept_3_3 2 72 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 283 (allA_of_3_1 71 71 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 283 (allA_succ_of_accept 69 70 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 283 (accept_3_3 68 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 283 (accept_3_3 65 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 283 (accept_3_3 62 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 283 (accept_3_3 59 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 283 (Polychromatic418967fa.accept_13_6_5_10_1_1213 58 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 283 (accept_3_3 56 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 283 (Polychromatic418967fa.accept_13_2_5_10_1_250 54 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 283 (accept_3_3 53 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 283 (accept_3_3 50 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 283 (accept_3_3 47 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 283 (accept_3_3 44 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 283 (Polychromatic418967fa.accept_13_4_5_10_1_1247 43 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 283 (accept_3_3 41 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 283 (accept_3_3 38 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 283 (Polychromatic418967fa.accept_16_4_6_11_1_3753 36 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 283 (accept_3_3 35 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 70 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 283 (accept_3_3 32 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 283 (accept_3_3 29 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 283 (accept_3_3 26 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 283 (accept_3_3 23 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 283 (Polychromatic418967fa.accept_20_2_10_3_1_9059 22 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 283 (accept_3_3 20 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 283 (accept_3_3 17 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 283 (accept_3_3 14 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 283 (accept_3_3 11 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 283 (accept_3_3 8 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 70 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 283 (accept_3_3 5 70 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 70 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 283 (accept_3_3 2 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 283
  (allA_succ_of_accept 68 69 283 (accept_3_3 68 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 283 (accept_3_3 65 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 283 (accept_3_3 62 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 283 (accept_3_3 59 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 283 (accept_3_3 56 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 283 (accept_3_3 53 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 283 (accept_3_3 50 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 283 (accept_3_3 47 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 283
  (Polychromatic418967fa.accept_13_6_4_10_1_660 45 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 283 (accept_3_3 44 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 283 (accept_3_3 41 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 283 (accept_3_3 38 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 283 (accept_3_3 35 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 283
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 33 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 283 (accept_3_3 32 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 283 (accept_3_3 29 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 283
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 283 (accept_3_3 26 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 283 (accept_3_3 23 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 283 (accept_3_3 20 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 283 (accept_3_3 17 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 283 (accept_3_3 14 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 283 (Polychromatic418967fa.accept_25_13_19_8_1_10561 13 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 283 (accept_3_3 11 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 283 (accept_3_3 8 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 283 (accept_3_3 5 69 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  69 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 283 (accept_3_3 2 69 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 69
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 283 (allA_of_3_1 68 68 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 283 (allA_succ_of_accept 66 67 283
  (Polychromatic418967fa.accept_10_6_7_3_1_547 66 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 283 (accept_3_3 65 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 283 (Polychromatic418967fa.accept_13_11_2_10_1_4399 63 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 283 (accept_3_3 62 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 283 (Polychromatic418967fa.accept_19_4_10_17_1_5194 61 67
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 283
  (Polychromatic418967fa.accept_13_8_2_10_1_652 60 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 283 (accept_3_3 59 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 58 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 283 (accept_3_3 56 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 283
  (Polychromatic418967fa.accept_10_4_7_3_1_54 54 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 283 (accept_3_3 53 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 283 (Polychromatic418967fa.accept_25_2_17_8_1_17338 52 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 283 (Polychromatic418967fa.accept_13_12_2_10_1_2698 51 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 283 (accept_3_3 50 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365 49 67
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 283 (accept_3_3 47 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 46 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 283 (accept_3_3 44 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 283
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 283 (accept_3_3 41 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 283 (Polychromatic418967fa.accept_16_8_3_11_1_4763 40 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 283 (Polychromatic418967fa.accept_15_9_7_13_1_1664 39 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 283 (accept_3_3 38 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 67 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 283 (accept_3_3 35 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 283 (Polychromatic418967fa.accept_22_11_1_19_1_14315 33 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 283 (accept_3_3 32 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 283 (Polychromatic418967fa.accept_13_5_2_10_1_248 31 67 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 283
  (Polychromatic418967fa.accept_16_14_3_11_1_5969 30 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 283 (accept_3_3 29 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 283 (Polychromatic418967fa.accept_23_5_21_7_1_17337 28 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 283 (accept_3_3 26 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 283
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 283 (accept_3_3 23 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 283 (Polychromatic418967fa.accept_13_8_2_10_1_652 21 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 283 (accept_3_3 20 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 283
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 283 (accept_3_3 17 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 283 (accept_3_3 14 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 283
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 283 (accept_3_3 11 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 283 (Polychromatic418967fa.accept_20_10_7_3_1_16094 10 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 283 (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 283 (accept_3_3 8 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 67 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 283 (accept_3_3 5 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  283 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 67 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 283 (Polychromatic418967fa.accept_13_3_2_10_1_2697 3 67 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 283 (accept_3_3 2 67 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 67 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 283 (allA_succ_of_accept 65 66
  283 (accept_3_3 65 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 283
  (Polychromatic418967fa.accept_9_1_3_4_1_47 64 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 283 (Polychromatic418967fa.accept_13_11_1_10_1_648 63 66 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 283 (accept_3_3 62 66 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 60
  66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 283 (accept_3_3 59 66
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 283
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 66 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 283 (accept_3_3 56 66 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 66 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 283 (Polychromatic418967fa.accept_16_6_2_11_1_7132
  54 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 283 (accept_3_3 53
  66 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 52 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 66 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 66 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 283 (accept_3_3 50 66 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 66 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  48 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 283 (accept_3_3 47
  66 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 283
  (Polychromatic418967fa.accept_9_1_3_4_1_47 46 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 66 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 283 (accept_3_3 44 66 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 66 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 42
  66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 283 (accept_3_3 41 66
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 283
  (Polychromatic418967fa.accept_19_2_9_17_1_626 40 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 66 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 66 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 283 (accept_3_3 38 66 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 66 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 283
  (Polychromatic418967fa.accept_21_15_3_10_1_8533 36 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 283 (accept_3_3 35 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  66 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 283 (accept_3_3 32 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 283 (Polychromatic418967fa.accept_25_6_16_8_1_15750 31 66 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 283
  (Polychromatic418967fa.accept_13_4_1_10_1_693 30 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 66 283 (accept_3_3 29 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  66 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 66 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 283 (accept_3_3 26 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 283 (accept_3_3 23 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  66 283 (Polychromatic418967fa.accept_13_9_1_10_1_647 22 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 66 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 283 (accept_3_3 20 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 66 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 283
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 283 (accept_3_3 17 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  66 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 283 (accept_3_3 14 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 283
  (Polychromatic418967fa.accept_21_12_3_10_1_8575 12 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 66 283 (accept_3_3 11 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  66 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 66 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 283 (accept_3_3 8 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 283 (accept_3_3 5 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  283 (Polychromatic418967fa.accept_13_4_1_10_1_693 4 66 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 66 283 (Polychromatic418967fa.accept_18_3_12_13_1_3307 3 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 283 (accept_3_3 2 66 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 283 (allA_of_3_1 65 65 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 283 (allA_succ_of_accept 63 64 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 283 (accept_3_3 62 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 283 (accept_3_3 59 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 64 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 283 (accept_3_3 56 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 55 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 283 (accept_3_3 53 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 64 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 283 (accept_3_3 50 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 283 (accept_3_3 47 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 64 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 283 (accept_3_3 44 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 283 (accept_3_3 41 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 64 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 283 (accept_3_3 38 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 283 (Polychromatic418967fa.accept_15_6_4_13_1_403 36 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 283 (accept_3_3 35 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 64 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 283 (accept_3_3 32 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 283 (Polychromatic418967fa.accept_25_6_14_8_1_17336 31 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 283 (accept_3_3 29 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 283 (Polychromatic418967fa.accept_13_2_12_10_1_2649 28 64 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 283 (accept_3_3 26 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 283 (accept_3_3 23 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 64 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 283 (accept_3_3 20 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 283 (accept_3_3 17 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 64 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 283 (accept_3_3 14 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 283 (Polychromatic418967fa.accept_19_13_7_17_1_9441 13 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 283 (accept_3_3 11 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 64 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 283 (accept_3_3 8 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 64 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 283 (accept_3_3 5 64 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 64 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 283 (accept_3_3 2 64 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 283 (Polychromatic418967fa.accept_18_1_10_13_1_500
  1 64 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 283 (allA_succ_of_accept 62 63 283
  (accept_3_3 62 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 283
  (Polychromatic418967fa.accept_15_1_3_13_1_2548 61 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 63 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 283 (accept_3_3 59 63 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 63 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 283 (Polychromatic418967fa.accept_12_9_3_7_1_924
  57 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 283 (accept_3_3 56
  63 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 283
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 55 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 283 (Polychromatic418967fa.accept_13_2_11_10_1_1881 54 63 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 283 (accept_3_3 53 63 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 63 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 283
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 63 283 (accept_3_3 50 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 283 (Polychromatic418967fa.accept_16_1_15_11_1_356 49 63 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 63 283 (Polychromatic418967fa.accept_17_14_12_11_1_4063 48 63
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 283 (accept_3_3 47 63 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 283 (accept_3_3 44 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 43 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 283 (Polychromatic418967fa.accept_13_3_11_10_1_2647 42 63 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 283 (accept_3_3 41 63 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 283
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 283 (accept_3_3 38 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 283 (Polychromatic418967fa.accept_19_18_6_17_1_8078 37 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 283 (accept_3_3 35 63 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 283 (accept_3_3 32 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 283 (Polychromatic418967fa.accept_15_1_3_13_1_2548 31 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 30 63 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 283 (accept_3_3 29 63 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 283
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 283 (accept_3_3 26 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 283 (Polychromatic418967fa.accept_13_12_11_10_1_2711 25 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 283 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 63 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 283 (accept_3_3 23 63 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 63 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 283 (accept_3_3 20 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 283 (Polychromatic418967fa.accept_16_3_15_11_1_2676 19 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 283 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 63 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 283 (accept_3_3 17 63 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 283
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 283 (accept_3_3 14 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 283 (Polychromatic418967fa.accept_17_13_12_11_1_2947 13 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 283 (accept_3_3 11 63 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 63 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 283 (accept_3_3 8 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  283 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 283 (Polychromatic418967fa.accept_17_6_12_11_1_5231 6 63 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 283 (accept_3_3 5 63 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 283
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 283 (accept_3_3 2 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  283 (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 63 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 283
  (allA_of_3_1 62 62 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 283 (allA_succ_of_accept 60 61 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 283 (accept_3_3 59 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 283 (accept_3_3 56 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 61 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 283 (accept_3_3 53 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 52 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 283 (accept_3_3 50 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 283 (Polychromatic418967fa.accept_19_11_4_17_1_2617 49 61 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 283 (accept_3_3 47 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 61 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 283 (accept_3_3 44 61 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 61 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 283 (accept_3_3 41 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 40 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 283 (accept_3_3 38 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 61 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 283 (accept_3_3 35 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 283 (accept_3_3 32 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 283 (Polychromatic418967fa.accept_23_8_15_7_1_7758 31 61 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 283 (accept_3_3 29 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 283 (accept_3_3 26 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 61 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 283 (accept_3_3 23 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 283 (accept_3_3 20 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 283 (accept_3_3 17 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 283 (accept_3_3 14 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 283 (Polychromatic418967fa.accept_19_13_4_17_1_5166 13 61 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 283 (accept_3_3 11 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 283 (accept_3_3 8 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 283 (Polychromatic418967fa.accept_21_7_19_10_1_8567 7 61 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 283 (accept_3_3 5 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  283 (Polychromatic418967fa.accept_17_4_10_11_1_6472 4 61 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 283 (accept_3_3 2 61 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 283 (allA_succ_of_accept 59 60 283
  (accept_3_3 59 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 283
  (Polychromatic418967fa.accept_11_3_5_8_1_458 58 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 60 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 283 (accept_3_3 56 60 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 60 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 60 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 283 (Polychromatic418967fa.accept_13_2_8_10_1_1902
  54 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 283 (accept_3_3 53
  60 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 283
  (Polychromatic418967fa.accept_9_7_6_4_1_483 52 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 60 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 60 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 283 (accept_3_3 50 60 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 60 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 49 60 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 48
  60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 283 (accept_3_3 47 60
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 283 (Polychromatic418967fa.accept_9_1_6_4_1_49
  46 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 60 283
  (Polychromatic418967fa.accept_18_9_6_13_1_4499 45 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 60 283 (accept_3_3 44 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  60 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 60 283 (Polychromatic418967fa.accept_16_10_12_11_1_346 42 60 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 283 (accept_3_3 41 60 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 283 (Polychromatic418967fa.accept_16_8_12_11_1_3697 40 60
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 60 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 60 283 (accept_3_3 38 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  60 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 60 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 60 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 283 (accept_3_3 35 60 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 60 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 283
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 60 283 (accept_3_3 32 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  60 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 60 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 60 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 283 (accept_3_3 29 60 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 60 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 60 283 (accept_3_3 26 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  60 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 60 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 60 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 283 (accept_3_3 23 60 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 60 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 60 283 (accept_3_3 20 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  60 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 60 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 60 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 283 (accept_3_3 17 60 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 60 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 60 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 60 283 (accept_3_3 14 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  60 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 60 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 60 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 283 (accept_3_3 11 60 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 60 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 60 283
  (Polychromatic418967fa.accept_18_9_6_13_1_4499 9 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 60 283 (accept_3_3 8 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60
  283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 60 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 60 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 283 (accept_3_3 5 60 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 60 283 (Polychromatic418967fa.accept_13_4_8_10_1_671 4 60 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  60 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 283 (accept_3_3 2 60 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 283 (allA_of_3_1 59 59 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 283 (allA_succ_of_accept 57 58 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 283 (accept_3_3 56 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 58 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 283 (accept_3_3 53 58 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 283 (accept_3_3 50 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 58 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 283 (accept_3_3 47 58 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 283 (accept_3_3 44 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 283 (Polychromatic418967fa.accept_13_3_6_10_1_2658 42 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 283 (accept_3_3 41 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 58 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 283 (accept_3_3 38 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 58 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 283 (accept_3_3 35 58 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 283 (accept_3_3 32 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 283 (Polychromatic418967fa.accept_13_4_6_10_1_1199 30 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 283 (accept_3_3 29 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 58 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 283 (accept_3_3 26 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 283 (Polychromatic418967fa.accept_21_3_16_10_1_3911 24 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 283 (accept_3_3 23 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 58 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 283 (accept_3_3 20 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 283 (accept_3_3 17 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 58 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 283 (accept_3_3 14 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 58 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 283 (accept_3_3 11 58 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 283 (Polychromatic418967fa.accept_18_10_4_13_1_3296 10 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 283 (accept_3_3 8 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  283 (Polychromatic418967fa.accept_18_7_4_13_1_3315 7 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 58 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 58 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 283 (accept_3_3 5 58 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 58 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 58 283 (accept_3_3 2 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58
  283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 283 (allA_succ_of_accept 56
  57 283 (accept_3_3 56 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 283
  (Polychromatic418967fa.accept_9_1_3_4_1_47 55 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 283 (accept_3_3 53 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 51
  57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 283 (accept_3_3 50 57
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 283
  (Polychromatic418967fa.accept_11_5_2_8_1_866 49 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 283 (Polychromatic418967fa.accept_15_3_12_13_1_2549 48 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 283 (accept_3_3 47 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 283 (Polychromatic418967fa.accept_10_5_7_3_1_561
  45 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 283 (accept_3_3 44
  57 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 283 (accept_3_3 41 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 39
  57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 283 (accept_3_3 38 57
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 283 (accept_3_3 35 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 283 (accept_3_3 32 57
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 283
  (Polychromatic418967fa.accept_15_1_12_13_1_944 31 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 283 (accept_3_3 29 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 283 (Polychromatic418967fa.accept_11_5_2_8_1_866
  27 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 283 (accept_3_3 26
  57 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 283 (accept_3_3 23 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 283 (Polychromatic418967fa.accept_13_8_5_10_1_2701
  21 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 283 (accept_3_3 20
  57 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 283 (accept_3_3 17 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 15
  57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 283 (accept_3_3 14 57
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 283
  (Polychromatic418967fa.accept_17_13_6_11_1_4014 13 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 283 (accept_3_3 11 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 9
  57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 283 (accept_3_3 8 57 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 283 (accept_3_3 5 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 283 (accept_3_3 2 57 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 57 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 283 (allA_of_3_1 56 56 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 283
  (allA_succ_of_accept 54 55 283 (Polychromatic418967fa.accept_13_2_3_10_1_658 54 55 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 283 (accept_3_3 53 55 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 51
  55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 283 (accept_3_3 50 55
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 283
  (Polychromatic418967fa.accept_15_4_10_13_1_2565 49 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 283 (accept_3_3 47 55 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 283 (Polychromatic418967fa.accept_13_6_3_10_1_698
  45 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 283 (accept_3_3 44
  55 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 283
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 55 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 55 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 283 (accept_3_3 41 55 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 55 283 (Polychromatic418967fa.accept_17_6_4_11_1_4072 40 55 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 283 (accept_3_3 38 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 283 (accept_3_3 35 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 283 (accept_3_3 32 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 283 (accept_3_3 29 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 55 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 283
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 283 (accept_3_3 26 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 283 (accept_3_3 23 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 55 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 283 (accept_3_3 20 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 19 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 283 (accept_3_3 17 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 55 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 283 (accept_3_3 14 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 283 (Polychromatic418967fa.accept_22_13_11_19_1_8148 13 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 283 (accept_3_3 11 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 283 (Polychromatic418967fa.accept_14_10_13_3_1_2552 10 55 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 283 (accept_3_3 8 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 283 (accept_3_3 5 55 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 55 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 283 (accept_3_3 2 55 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 283 (Polychromatic418967fa.accept_15_1_10_13_1_939
  1 55 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 283 (allA_succ_of_accept 53 54 283
  (accept_3_3 53 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 283
  (Polychromatic418967fa.accept_15_7_9_13_1_3451 52 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 54 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 54 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 283 (accept_3_3 50 54 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 54 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681
  48 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 283 (accept_3_3 47
  54 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 283
  (Polychromatic418967fa.accept_19_8_16_17_1_6552 46 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 54 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 283 (accept_3_3 44 54 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 54 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 283 (Polychromatic418967fa.accept_11_9_10_8_1_444
  42 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 54 283 (accept_3_3 41
  54 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 283
  (Polychromatic418967fa.accept_19_2_16_17_1_12112 40 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 283 (accept_3_3 38 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 283 (accept_3_3 35 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 283 (Polychromatic418967fa.accept_13_8_2_10_1_652 34 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 283 (accept_3_3 32 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 54 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 283 (accept_3_3 29 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 283 (Polychromatic418967fa.accept_20_8_14_3_1_9074 28 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 283 (accept_3_3 26 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 283
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 283 (accept_3_3 23 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 283 (accept_3_3 20 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 54 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 283
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 283 (accept_3_3 17 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 283 (accept_3_3 14 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 283
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 283 (accept_3_3 11 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 283 (Polychromatic418967fa.accept_17_10_3_11_1_6482 10 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 283 (accept_3_3 8 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 54 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 283
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 283 (accept_3_3 5 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 4 54 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 283 (Polychromatic418967fa.accept_13_3_2_10_1_2697 3 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 283 (accept_3_3 2 54 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 283 (allA_of_3_1 53 53 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 283 (allA_succ_of_accept 51 52 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 283 (accept_3_3 50 52 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 283 (Polychromatic418967fa.accept_14_7_10_3_1_1034
  49 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 283 (accept_3_3 47 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 283 (accept_3_3 44 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 283 (Polychromatic418967fa.accept_19_5_14_17_1_6550 43 52 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 283 (accept_3_3 41 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 283 (Polychromatic418967fa.accept_16_8_4_11_1_2687 40 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 283 (accept_3_3 38 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 52 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 283
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 36 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 283 (accept_3_3 35 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 283 (accept_3_3 32 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 52 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 283 (accept_3_3 29 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 283 (accept_3_3 26 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 52 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 283 (accept_3_3 23 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 283 (accept_3_3 20 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 52 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 283
  (Polychromatic418967fa.accept_22_18_8_19_1_8113 18 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 283 (accept_3_3 17 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 283 (Polychromatic418967fa.accept_19_16_14_17_1_3863 16 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 283 (accept_3_3 14 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 283 (Polychromatic418967fa.accept_14_13_10_3_1_1037 13 52 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 283 (accept_3_3 11 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 283 (accept_3_3 8 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 52 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 283 (accept_3_3 5 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  283 (Polychromatic418967fa.accept_27_4_25_13_1_17335 4 52 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 283 (accept_3_3 2 52 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 52 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  283)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 283 (allA_succ_of_accept 50 51 283 (accept_3_3
  50 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 283
  (Polychromatic418967fa.accept_15_4_6_13_1_956 49 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 283 (accept_3_3 47 51 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 51 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 283 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 283 (accept_3_3 44
  51 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 51 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 283 (accept_3_3 41 51 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 39
  51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 283 (accept_3_3 38 51
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 283 (Polychromatic418967fa.accept_9_1_6_4_1_49
  37 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 283 (accept_3_3 35 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 51 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 283 (accept_3_3 32 51 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 283 (Polychromatic418967fa.accept_16_15_3_11_1_5997 31 51 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 283 (accept_3_3 29 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 283 (accept_3_3 26 51 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 51 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 283
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 283 (accept_3_3 23 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 283 (accept_3_3 20 51 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19
  51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 283
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 283 (accept_3_3 17 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 283 (accept_3_3 14 51 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 51 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 283 (accept_3_3 11 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 51 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 283 (accept_3_3 8 51 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 51 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 283 (accept_3_3 5 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 51 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 283 (accept_3_3 2 51 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 51 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 283)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 283 (allA_of_3_1 50 50 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 283
  (allA_succ_of_accept 48 49 283 (Polychromatic418967fa.accept_25_23_24_8_1_17334 48 49 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 283 (accept_3_3 47 49 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 283 (Polychromatic418967fa.accept_21_3_7_10_1_7002
  45 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 283 (accept_3_3 44
  49 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 283
  (Polychromatic418967fa.accept_19_5_11_17_1_6536 43 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 283 (accept_3_3 41 49 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 40 49 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 283
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 283 (accept_3_3 38 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 283 (Polychromatic418967fa.accept_19_18_11_17_1_12083 37 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 49 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 283 (accept_3_3 35 49 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 283
  (Polychromatic418967fa.accept_17_16_15_11_1_10421 33 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 49 283 (accept_3_3 32 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 49 283 (Polychromatic418967fa.accept_16_15_1_11_1_3747 31 49 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 283 (accept_3_3 29 49 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 283
  (Polychromatic418967fa.accept_16_12_1_11_1_5958 28 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 49 283 (Polychromatic418967fa.accept_19_8_11_17_1_9503 27 49 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 283 (accept_3_3 26 49 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 49 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 49 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907
  24 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 283 (accept_3_3 23
  49 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 49 283 (Polychromatic418967fa.accept_15_6_4_13_1_403 21 49 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 283 (accept_3_3 20 49 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 49 283 (Polychromatic418967fa.accept_20_19_9_3_1_10554 19 49 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 283 (accept_3_3 17 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 283 (Polychromatic418967fa.accept_16_15_1_11_1_3747 15 49 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 283 (accept_3_3 14 49 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 49 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 283
  (Polychromatic418967fa.accept_16_12_1_11_1_5958 12 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 283 (accept_3_3 11 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 283 (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 49 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 283 (accept_3_3 8 49 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 283 (Polychromatic418967fa.accept_24_7_1_19_1_2203 7 49 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 283 (accept_3_3 5 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 49 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 49 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 283 (accept_3_3 2 49 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 283 (Polychromatic418967fa.accept_21_1_7_10_1_2596 1 49 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 283)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 283 (allA_succ_of_accept 47 48 283 (accept_3_3 47 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 48 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 48 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 283 (accept_3_3 44 48 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 43
  48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 283 (accept_3_3 41 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  48 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 283 (accept_3_3 38 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 283
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 283 (accept_3_3 35 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 283 (accept_3_3 32 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 48 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 283 (accept_3_3 29 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 283 (accept_3_3 26 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 283 (accept_3_3 23 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 283 (Polychromatic418967fa.accept_25_22_23_8_1_17333 22 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 283 (accept_3_3 20 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 283 (accept_3_3 17 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 283 (accept_3_3 14 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 283 (Polychromatic418967fa.accept_20_13_8_3_1_11818 13 48 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 283
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 283 (accept_3_3 11 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 283 (accept_3_3 8 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 283 (accept_3_3 5 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 48 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 283 (Polychromatic418967fa.accept_17_3_14_11_1_5243 3 48 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 283 (accept_3_3 2 48 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 283)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 283 (allA_of_3_1 47 47 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 283 (allA_succ_of_accept 45 46
  283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 283 (accept_3_3 44 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 283 (accept_3_3 41 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 46 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 283 (accept_3_3 38 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 283 (accept_3_3 35 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 46 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 283 (accept_3_3 32 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 283 (Polychromatic418967fa.accept_17_14_12_11_1_4063 31 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 283 (accept_3_3 29 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 46 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 283 (accept_3_3 26 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 283 (accept_3_3 23 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 46 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 283 (accept_3_3 20 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 283 (accept_3_3 17 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 46 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 283 (accept_3_3 14 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 283 (accept_3_3 11 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 46 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 283 (accept_3_3 8 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 46 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 283 (accept_3_3 5 46 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 46 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 283 (accept_3_3 2 46 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  283)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 283 (allA_succ_of_accept 44 45 283 (accept_3_3 44 45
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 283
  (Polychromatic418967fa.accept_13_4_6_10_1_1199 43 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 283 (accept_3_3 41 45 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 283 (Polychromatic418967fa.accept_12_3_9_7_1_472
  39 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 283 (accept_3_3 38
  45 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 283
  (Polychromatic418967fa.accept_10_7_5_3_1_542 37 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 45 283 (Polychromatic418967fa.accept_21_15_3_10_1_8533 36 45 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 283 (accept_3_3 35 45 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 45 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 283
  (Polychromatic418967fa.accept_21_12_3_10_1_8575 33 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 283 (accept_3_3 32 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  45 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 45 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 283 (accept_3_3 29 45 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 283
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 283 (accept_3_3 26 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  45 283 (Polychromatic418967fa.accept_13_12_6_10_1_667 25 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 283 (Polychromatic418967fa.accept_16_8_13_11_1_4772 24 45 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 283 (accept_3_3 23 45 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 283
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 21 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 283 (accept_3_3 20 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  45 283 (Polychromatic418967fa.accept_27_19_18_13_1_13724 19 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 283 (accept_3_3 17 45 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 283
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 283 (accept_3_3 14 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 283 (Polychromatic418967fa.accept_19_13_7_17_1_9441 13 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 45 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 283 (accept_3_3 11 45 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 283
  (Polychromatic418967fa.accept_13_9_6_10_1_666 9 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 283 (accept_3_3 8 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  283 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 45 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 283 (accept_3_3 5 45 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 45 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 3
  45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 283 (accept_3_3 2 45 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 283 (Polychromatic418967fa.accept_20_1_5_3_1_7397 1
  45 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  283))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 283 (allA_of_3_1 44 44 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 283 (allA_succ_of_accept 42 43 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 283 (accept_3_3 41 43 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40
  43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 283 (accept_3_3 38 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 283 (Polychromatic418967fa.accept_17_2_9_11_1_4057 36 43 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 283 (accept_3_3 35 43 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 283 (Polychromatic418967fa.accept_13_8_4_10_1_4358 34 43
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 283 (accept_3_3 32 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 43 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 283 (accept_3_3 29 43 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 283
  (Polychromatic418967fa.accept_13_1_4_10_1_622 27 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 283 (accept_3_3 26 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 43 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 283 (accept_3_3 23 43 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 283 (Polychromatic418967fa.accept_18_4_7_13_1_3303 22 43 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 283 (accept_3_3 20 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 43 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 283 (accept_3_3 17 43 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 43 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 283 (accept_3_3 14 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 283 (Polychromatic418967fa.accept_21_13_1_10_1_5377 13 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 283 (accept_3_3 11 43 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 43 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 283 (accept_3_3 8 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  283 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 43 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 43 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 283 (accept_3_3 5 43 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 43 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 283 (accept_3_3 2 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43
  283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 43 283))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 283 (allA_succ_of_accept 41 42 283
  (accept_3_3 41 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 283
  (Polychromatic418967fa.accept_15_10_12_13_1_2585 40 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 283 (accept_3_3 38 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 283
  (Polychromatic418967fa.accept_17_2_8_11_1_1041 36 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 283 (accept_3_3 35 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 283 (accept_3_3 32 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 42 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 283 (accept_3_3 29 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 283 (Polychromatic418967fa.accept_18_9_6_13_1_4499 27 42 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 283 (accept_3_3 26 42 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 283
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 283 (accept_3_3 23 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 283 (Polychromatic418967fa.accept_25_22_17_8_1_17332 22 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 283 (accept_3_3 20 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 283 (accept_3_3 17 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 283 (accept_3_3 14 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 283 (accept_3_3 11 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 283 (accept_3_3 8 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 42 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 283
  (Polychromatic418967fa.accept_13_6_3_10_1_698 6 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 283 (accept_3_3 5 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  283 (Polychromatic418967fa.accept_28_4_14_3_1_17331 4 42 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 42 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 283 (accept_3_3 2 42 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 283))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 41 283 (allA_of_3_1 41 41 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 283
  (allA_succ_of_accept 39 40 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 40 283 (accept_3_3 38 40 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 40 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 40 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 40 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 36
  40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 283 (accept_3_3 35 40
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 283
  (Polychromatic418967fa.accept_12_10_4_7_1_948 34 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 40 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 283 (accept_3_3 32 40 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 40 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 40 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 40 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 40 283 (accept_3_3 29 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  40 283 (Polychromatic418967fa.accept_16_12_8_11_1_2695 28 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 40 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 283 (accept_3_3 26 40 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 40 283 (Polychromatic418967fa.accept_18_7_4_13_1_3315 25 40 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 40 283
  (Polychromatic418967fa.accept_13_11_1_10_1_648 24 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 40 283 (accept_3_3 23 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  40 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 40 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 40 283 (accept_3_3 20 40 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 40 283 (Polychromatic418967fa.accept_14_5_12_3_1_3397 19 40 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 283
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 40 283 (accept_3_3 17 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  40 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 40 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 40 283 (accept_3_3 14 40 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 283 (Polychromatic418967fa.accept_16_13_8_11_1_4785 13 40 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 283
  (Polychromatic418967fa.accept_15_12_10_13_1_4497 12 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 40 283 (accept_3_3 11 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 40 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 40 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 283 (accept_3_3 8 40 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 283 (Polychromatic418967fa.accept_18_7_4_13_1_3315
  7 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 283
  (Polychromatic418967fa.accept_23_6_17_7_1_9295 6 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 40 283 (accept_3_3 5 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 40
  283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 40 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 40 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 283 (accept_3_3 2 40 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 40 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 283))))))))))))))))))))))))))))))))))))))))
  (allB_succ 39 283 (allA_succ_of_accept 38 39 283 (accept_3_3 38 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 39 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 283 (accept_3_3 35 39 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34
  39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 283 (accept_3_3 32 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 283 (Polychromatic418967fa.accept_16_15_7_11_1_3760 31 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 283 (Polychromatic418967fa.accept_18_12_3_13_1_4494 30 39 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 283 (accept_3_3 29 39 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 283 (accept_3_3 26 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 283 (accept_3_3 23 39 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 283 (accept_3_3 20 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 39 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 283 (accept_3_3 17 39 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 283 (accept_3_3 14 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 39 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 283 (accept_3_3 11 39 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 283 (accept_3_3 8 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 39 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 283 (accept_3_3 5 39 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3
  39 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 283 (accept_3_3 2 39 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 39
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  283))))))))))))))))))))))))))))))))))))))) (allB_succ 38 283 (allA_of_3_1 38 38 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 283 (allA_succ_of_accept 36 37 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 283 (accept_3_3 35 37 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 283 (accept_3_3 32 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 283 (Polychromatic418967fa.accept_17_14_3_11_1_11591 31 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 283 (accept_3_3 29 37 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 283 (Polychromatic418967fa.accept_13_2_11_10_1_1881 28 37 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 283 (accept_3_3 26 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 37 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 283 (accept_3_3 23 37 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 283 (accept_3_3 20 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 283 (accept_3_3 17 37 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 283 (accept_3_3 14 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 283 (accept_3_3 11 37 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 283
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 283 (accept_3_3 8 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 283 (accept_3_3 5 37 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 37 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 283 (accept_3_3 2 37 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  37 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  283))))))))))))))))))))))))))))))))))))) (allB_succ 36 283 (allA_succ_of_accept 35 36 283 (accept_3_3 35 36 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 283 (Polychromatic418967fa.accept_15_4_6_13_1_956
  34 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 36 283 (accept_3_3 32 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  36 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 36 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 36 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 283 (accept_3_3 29 36 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 36 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 283
  (Polychromatic418967fa.accept_10_7_6_3_1_927 27 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 36 283 (accept_3_3 26 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  36 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 36 283 (Polychromatic418967fa.accept_16_8_4_11_1_2687 24 36 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 283 (accept_3_3 23 36 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 283 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 36 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 283
  (Polychromatic418967fa.accept_24_21_12_19_1_17330 21 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 283 (accept_3_3 20 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 36 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 36 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 283 (accept_3_3 17 36 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16
  36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 36 283 (accept_3_3 14 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  36 283 (Polychromatic418967fa.accept_20_13_16_3_1_4479 13 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 36 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 36 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 283 (accept_3_3 11 36 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 283 (Polychromatic418967fa.accept_25_10_11_8_1_17329 10 36 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 36 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 36 283 (accept_3_3 8 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36
  283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 36 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 36 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 283 (accept_3_3 5 36 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 36 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 36 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 283 (Polychromatic418967fa.accept_17_3_2_11_1_1895
  3 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 283 (accept_3_3 2 36
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 283
  (Polychromatic418967fa.accept_21_1_15_10_1_11607 1 36 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 283)))))))))))))))))))))))))))))))))))) (allB_succ 35 283 (allA_of_3_1 35 35 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 283 (allA_succ_of_accept 33 34 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 283 (accept_3_3 32 34 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 34 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363
  31 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 34 283 (accept_3_3 29 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  34 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 34 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 283 (accept_3_3 26 34 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 34 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 34 283 (accept_3_3 23 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  34 283 (Polychromatic418967fa.accept_16_6_2_11_1_7132 22 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 34 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 34 283 (accept_3_3 20 34 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 34 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 34 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 34 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 34 283 (accept_3_3 17 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  34 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 34 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 34 283 (accept_3_3 14 34 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 34 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 34 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 34 283 (accept_3_3 11 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  34 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 34 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 34 283 (accept_3_3 8 34 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 34 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 34 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 34 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 34 283 (accept_3_3 5 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 34
  283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 34 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 34 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 283 (accept_3_3 2 34 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 34 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 283)))))))))))))))))))))))))))))))))) (allB_succ 33 283
  (allA_succ_of_accept 32 33 283 (accept_3_3 32 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  33 283 (Polychromatic418967fa.accept_15_1_3_13_1_2548 31 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 33 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 283 (accept_3_3 29 33 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 283 (accept_3_3 26 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 33 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 283 (accept_3_3 23 33 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 283 (accept_3_3 20 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 283 (accept_3_3 17 33 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 283 (accept_3_3 14 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 283 (Polychromatic418967fa.accept_22_13_11_19_1_8148 13 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 283 (accept_3_3 11 33 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 283 (accept_3_3 8 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 33 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 283 (accept_3_3 5 33 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  33 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 283 (accept_3_3 2 33 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  33 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 283)))))))))))))))))))))))))))))))))
  (allB_succ 32 283 (allA_of_3_1 32 32 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 283
  (allA_succ_of_accept 30 31 283 (Polychromatic418967fa.accept_13_4_5_10_1_1247 30 31 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 283 (accept_3_3 29 31 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 31 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 283
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 283 (accept_3_3 26 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 283 (Polychromatic418967fa.accept_19_5_12_17_1_8089 24 31 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 283 (accept_3_3 23 31 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 22 31 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 283
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 283 (accept_3_3 20 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 283 (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 31 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 283 (accept_3_3 17 31 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 283 (Polychromatic418967fa.accept_17_16_14_11_1_7836 16 31 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 283
  (Polychromatic418967fa.accept_13_2_5_10_1_250 15 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 283 (accept_3_3 14 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 283 (Polychromatic418967fa.accept_20_13_11_3_1_4509 13 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 31 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 283 (accept_3_3 11 31 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 31 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 283
  (Polychromatic418967fa.accept_23_9_8_7_1_9407 9 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 283 (accept_3_3 8 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  283 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 31 283 (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 31 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 283 (accept_3_3 5 31 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 31 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 283
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 3 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 283 (accept_3_3 2 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31
  283 (Polychromatic418967fa.accept_16_1_15_11_1_356 1 31 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 31 283))))))))))))))))))))))))))))))) (allB_succ 30 283 (allA_succ_of_accept 29 30 283
  (accept_3_3 29 30 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 283
  (Polychromatic418967fa.accept_9_1_3_4_1_47 28 30 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 30 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 30 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 283 (accept_3_3 26 30 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 30 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24
  30 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 283 (accept_3_3 23 30
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 30 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 30 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 283 (accept_3_3 20 30 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 30 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244
  18 30 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 283 (accept_3_3 17
  30 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 16 30 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 30 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 30 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 283 (accept_3_3 14 30 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 30 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12
  30 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 283 (accept_3_3 11 30
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 283 (Polychromatic418967fa.accept_9_1_3_4_1_47
  10 30 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 283 (accept_3_3 8 30 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30
  283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 30 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 30 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 30 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 283 (accept_3_3 5 30 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 30 283 (Polychromatic418967fa.accept_19_4_11_17_1_9505 4 30 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 283 (Polychromatic418967fa.accept_16_3_14_11_1_2654
  3 30 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 283 (accept_3_3 2 30
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  30 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 283))))))))))))))))))))))))))))))
  (allB_succ 29 283 (allA_of_3_1 29 29 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 283
  (allA_succ_of_accept 27 28 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 283 (accept_3_3 26 28 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 28 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24
  28 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 283 (accept_3_3 23 28
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 283
  (Polychromatic418967fa.accept_12_10_4_7_1_948 22 28 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 28 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 283 (accept_3_3 20 28 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 28 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 28 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 283
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 28 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 283 (accept_3_3 17 28 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  28 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 28 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 283 (accept_3_3 14 28 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 28 283 (Polychromatic418967fa.accept_19_13_9_17_1_8070 13 28 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 28 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 283 (accept_3_3 11 28 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 28 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 283 (accept_3_3 8 28 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 28 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 28 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 283 (accept_3_3 5 28 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  283 (Polychromatic418967fa.accept_16_4_12_11_1_2650 4 28 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 28 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 283 (accept_3_3 2 28 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 28 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 283)))))))))))))))))))))))))))) (allB_succ 27 283
  (allA_succ_of_accept 26 27 283 (accept_3_3 26 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  27 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 27 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 27 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 283 (accept_3_3 23 27 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 27 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 283 (accept_3_3 20 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 283 (Polychromatic418967fa.accept_25_19_2_8_1_12187 19 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 27 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 283 (accept_3_3 17 27 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 283
  (Polychromatic418967fa.accept_10_5_7_3_1_561 15 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 283 (accept_3_3 14 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 283 (Polychromatic418967fa.accept_21_12_6_10_1_14480 12 27 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 283 (accept_3_3 11 27 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 283 (accept_3_3 8 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  283 (Polychromatic418967fa.accept_24_7_3_19_1_17328 7 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 27 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 283 (accept_3_3 5 27 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 283
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 283 (accept_3_3 2 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  283 (Polychromatic418967fa.accept_15_1_12_13_1_944 1 27 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 283))))))))))))))))))))))))))) (allB_succ 26 283 (allA_of_3_1 26 26 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 283 (allA_succ_of_accept 24 25 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24
  25 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 283 (accept_3_3 23 25
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 283 (Polychromatic418967fa.accept_4_2_1_3_1_27
  22 25 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 25 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 283 (accept_3_3 20 25 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 25 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 283 (accept_3_3 17 25 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 25 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 25 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 283 (accept_3_3 14 25 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 25 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 283 (accept_3_3 11 25 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 283
  (Polychromatic418967fa.accept_13_9_12_10_1_242 9 25 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 283 (accept_3_3 8 25 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  283 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 25 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 283 (accept_3_3 5 25 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 25 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 25
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 283 (accept_3_3 2 25 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 283))))))))))))))))))))))))) (allB_succ
  24 283 (allA_succ_of_accept 23 24 283 (accept_3_3 23 24 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 283 (Polychromatic418967fa.accept_15_7_9_13_1_3451 22 24 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 283 (accept_3_3 20 24 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19
  24 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 24 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 283 (accept_3_3 17 24 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 24 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 283 (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 24 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 283 (accept_3_3 14 24 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 283 (Polychromatic418967fa.accept_14_13_10_3_1_1037 13 24
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 24 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 283 (accept_3_3 11 24 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 24 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 24 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 283 (accept_3_3 8 24 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 283
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 24 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 283 (accept_3_3 5 24 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 24 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 24 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 283 (accept_3_3 2 24 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 24 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 283)))))))))))))))))))))))) (allB_succ 23 283
  (allA_of_3_1 23 23 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 283 (allA_succ_of_accept 21 22 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 283 (accept_3_3 20 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 22 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 283 (accept_3_3 17 22 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 22 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 283 (accept_3_3 14 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 22 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 283 (accept_3_3 11 22 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 283 (Polychromatic418967fa.accept_18_10_4_13_1_3296 10 22 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 283 (accept_3_3 8 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  283 (Polychromatic418967fa.accept_17_7_5_11_1_2922 7 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 22 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 22 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 283 (accept_3_3 5 22 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 22 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 283 (accept_3_3 2 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22
  283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 283)))))))))))))))))))))) (allB_succ 21 283 (allA_succ_of_accept 20 21 283 (accept_3_3 20 21 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 21 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 283 (accept_3_3 17 21 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  21 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 21 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 283 (accept_3_3 14 21 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 283 (Polychromatic418967fa.accept_20_13_1_3_1_11831 13 21 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 283
  (Polychromatic418967fa.accept_10_2_1_3_1_233 12 21 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 283 (accept_3_3 11 21 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 21 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 283 (accept_3_3 8 21 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 21 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 283 (accept_3_3 5 21 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 21 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 283 (accept_3_3 2 21 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 21 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 283))))))))))))))))))))) (allB_succ 20 283 (allA_of_3_1 20 20
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 283 (allA_succ_of_accept 18 19 283
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 19 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 283 (accept_3_3 17 19 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 19 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 19 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 283 (accept_3_3 14 19 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 283 (Polychromatic418967fa.accept_23_13_19_7_1_17327 13 19 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 283 (accept_3_3 11 19 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 19 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 19 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 283 (accept_3_3 8 19 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 19 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 283 (accept_3_3 5 19 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 19 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 19 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 283 (accept_3_3 2 19 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 19 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 283))))))))))))))))))) (allB_succ 18 283
  (allA_succ_of_accept 17 18 283 (accept_3_3 17 18 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  18 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 18 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 18 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 18 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 283 (accept_3_3 14 18 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 283
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 18 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 18 283 (accept_3_3 11 18 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  18 283 (Polychromatic418967fa.accept_15_10_3_13_1_4480 10 18 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 18 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 283 (accept_3_3 8 18 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 18 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 18 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 283 (accept_3_3 5 18 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18
  283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 18 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 283 (Polychromatic418967fa.accept_21_3_18_10_1_10020 3 18 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 283 (accept_3_3 2 18 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 283)))))))))))))))))) (allB_succ 17 283
  (allA_of_3_1 17 17 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 283 (allA_succ_of_accept 15 16 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 283 (accept_3_3 14 16 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 16 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 16 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 283 (accept_3_3 11 16 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 16 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 283 (accept_3_3 8 16 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  283 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 16 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 16 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 283 (accept_3_3 5 16 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 283 (Polychromatic418967fa.accept_21_4_16_10_1_10019 4 16 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 283 (accept_3_3 2 16 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16
  283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 16 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 283)))))))))))))))) (allB_succ 15 283 (allA_succ_of_accept 14 15 283 (accept_3_3 14 15 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 283 (Polychromatic418967fa.accept_17_13_15_11_1_2936 13 15
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 15 283 (accept_3_3 11 15 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  15 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 15 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 15 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 283 (accept_3_3 8 15 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 15 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 283
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 15 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 283 (accept_3_3 5 15 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 15 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 283 (accept_3_3 2 15 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 15 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 283))))))))))))))) (allB_succ 14 283 (allA_of_3_1 14 14 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 283 (allA_succ_of_accept 12 13 283
  (Polychromatic418967fa.accept_17_12_13_11_1_2910 12 13 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 283 (accept_3_3 11 13 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 13 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 283 (accept_3_3 8 13 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 283 (Polychromatic418967fa.accept_17_7_13_11_1_2895
  7 13 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 283 (accept_3_3 5 13 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 13 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 283 (Polychromatic418967fa.accept_21_3_13_10_1_11614 3 13 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 283 (accept_3_3 2 13 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 283 (Polychromatic418967fa.accept_20_1_13_3_1_11838 1 13 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 283))))))))))))) (allB_succ 12 283 (allA_succ_of_accept 11 12
  283 (accept_3_3 11 12 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 283
  (Polychromatic418967fa.accept_9_1_3_4_1_47 10 12 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 283 (accept_3_3 8 12 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 6
  12 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 283 (accept_3_3 5 12 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4
  12 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 12 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 283 (accept_3_3 2 12 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 283)))))))))))) (allB_succ 11 283 (allA_of_3_1 11 11 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 283 (allA_succ_of_accept 9 10 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 283 (accept_3_3 8 10 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 10 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 283 (accept_3_3 5 10 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 10 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 10 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 283 (accept_3_3 2 10 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 283)))))))))) (allB_succ 9 283 (allA_succ_of_accept 8
  9 283 (accept_3_3 8 9 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 283
  (Polychromatic418967fa.accept_15_7_9_13_1_3451 7 9 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 283 (accept_3_3 5 9 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 9
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 283 (accept_3_3 2 9 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 9
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 283))))))))) (allB_succ 8 283
  (allA_of_3_1 8 8 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 283 (allA_succ_of_accept 6 7 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 283 (accept_3_3 5 7 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 7 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 7 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 283 (accept_3_3 2 7 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 283))))))) (allB_succ 6 283 (allA_succ_of_accept 5 6 283
  (accept_3_3 5 6 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 6 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 6 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 283 (accept_3_3 2 6 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 283)))))) (allB_succ 5 283 (allA_of_3_1 5 5 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 283 (allA_succ_of_accept 3 4 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 283 (accept_3_3 2 4 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 283)))) (allB_succ 3 283 (allA_succ_of_accept 2 3 283 (accept_3_3 2 3 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 3 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 283))) (allB_succ 2 283 (allA_of_3_1 2 2 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


