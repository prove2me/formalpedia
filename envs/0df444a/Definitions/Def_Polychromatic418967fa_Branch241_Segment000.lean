-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch241_Segment000
-- name    : Polychromatic418967fa_Branch241_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:39:15.289677+00:00
-- url     : https://prove2.me/theorems/77827ac8-9110-4d38-919d-0d56718f546a
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

def Polychromatic418967fa.branch_241_segment_000 : allB 123 241 :=
  allB_succ' 120 122 241 (Eq.refl Bool.true) (allA_of_3_1 120 122 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 121 241 (allA_succ_of_accept 120 121 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 120 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 241 (accept_3_3 119 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 121 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 118 121
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 117 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 121 241 (accept_3_3 116 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 121 241 (Polychromatic418967fa.accept_13_11_4_7_1_2419 115 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 121 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 114 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 241 (accept_3_3 113 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 241 (Polychromatic418967fa.accept_18_4_13_7_1_5395 112
  121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 121 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 111 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 121 241 (accept_3_3 110 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 121 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 109 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 121 241 (Polychromatic418967fa.accept_21_3_16_10_1_3911 108 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 121 241 (accept_3_3 107 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 121 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 106 121
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 105 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 121 241 (accept_3_3 104 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 121 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 121 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 102 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 241 (accept_3_3 101 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 100 121 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 241 (accept_3_3 98 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 241 (accept_3_3 95 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 94 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 93 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 241 (accept_3_3 92 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 241 (accept_3_3 89 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 241 (Polychromatic418967fa.accept_13_10_4_7_1_2465 88 121 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 87 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 241 (accept_3_3 86 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 241 (accept_3_3 83 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 241
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 81 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 241 (accept_3_3 80 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 241 (Polychromatic418967fa.accept_17_11_2_3_1_8468 79 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 241 (accept_3_3 77 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 241 (accept_3_3 74 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 241 (Polychromatic418967fa.accept_16_8_9_1_1_7753 72 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 241 (accept_3_3 71 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 241 (Polychromatic418967fa.accept_21_7_16_10_1_1349 70 121
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 241 (accept_3_3 68 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 241 (Polychromatic418967fa.accept_21_4_16_10_1_10019 67 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 121 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 241 (accept_3_3 65 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 121 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 241
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 63 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 241 (accept_3_3 62 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 241 (accept_3_3 59 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 241 (Polychromatic418967fa.accept_13_6_4_7_1_2464 58 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 241 (accept_3_3 56 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 241 (accept_3_3 53 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 241 (Polychromatic418967fa.accept_17_1_2_3_1_4668 52 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 51 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 241 (accept_3_3 50 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 241 (Polychromatic418967fa.accept_13_10_4_7_1_2465 49 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 241 (accept_3_3 47 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 241
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 45 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 241 (accept_3_3 44 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 241 (accept_3_3 41 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 241 (accept_3_3 38 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 241 (accept_3_3 35 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 241 (accept_3_3 32 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 241 (Polychromatic418967fa.accept_17_14_2_3_1_7172 31 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 241 (accept_3_3 29 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 241 (accept_3_3 26 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 241 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 241 (accept_3_3 23 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 241 (accept_3_3 20 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 241 (Polychromatic418967fa.accept_16_2_9_1_1_6404 18 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 241 (accept_3_3 17 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 121
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 241 (accept_3_3 14 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 241 (accept_3_3 11 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 241
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 241 (accept_3_3 8 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 241 (Polychromatic418967fa.accept_21_7_16_10_1_1349 7 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 241 (accept_3_3 5 121 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 241 (Polychromatic418967fa.accept_18_4_13_7_1_5395 4 121 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 241 (accept_3_3 2 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 121 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 241 (allA_succ_of_accept 119 120 241 (accept_3_3 119 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 120 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 118 120 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 120 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 117 120
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 241 (accept_3_3 116 120
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 120 241
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 115 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 120 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 114 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 120 241 (accept_3_3 113 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 120 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 112 120
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 241
  (Polychromatic418967fa.accept_16_15_8_1_1_9959 111 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 120 241 (accept_3_3 110 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 120 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 109 120 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 120 241 (Polychromatic418967fa.accept_13_4_3_7_1_2515 108 120
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 241 (accept_3_3 107 120
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 241
  (Polychromatic418967fa.accept_19_11_6_13_1_3477 106 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 120 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 105 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 120 241 (accept_3_3 104 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 120 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 103 120
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 120 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 102 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 120 241 (accept_3_3 101 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 120 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 120 241 (Polychromatic418967fa.accept_13_8_3_7_1_2455 99 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 120 241 (accept_3_3 98 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 120 241 (Polychromatic418967fa.accept_19_2_6_13_1_4941 97 120
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 120 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 96 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 120 241 (accept_3_3 95 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 120 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 94 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 120 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 93 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 241 (accept_3_3 92 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 120 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 91 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 120 241
  (Polychromatic418967fa.accept_21_6_15_10_1_2579 90 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 120 241 (accept_3_3 89 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 120 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 120 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 120 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 241 (accept_3_3 86 120 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 120 241 (Polychromatic418967fa.accept_9_4_3_7_1_296
  85 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 120 241
  (Polychromatic418967fa.accept_16_4_8_1_1_5257 84 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 120 241 (accept_3_3 83 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 120 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 120 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 120 241 (accept_3_3 80 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 120 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 120 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 120 241 (accept_3_3 77 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 120 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 120 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 120 241 (accept_3_3 74 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 120 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 120 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 120 241 (accept_3_3 71 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 120 241 (Polychromatic418967fa.accept_17_2_1_3_1_2357 70 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 120 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 241 (accept_3_3 68 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 120 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 120 241
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 66 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 120 241 (accept_3_3 65 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 120 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 120 241 (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 241 (accept_3_3 62 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 120 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 120 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 120 241 (accept_3_3 59 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 120 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 120 241 (Polychromatic418967fa.accept_16_9_8_1_1_1228 57 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 241 (accept_3_3 56 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 120 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 120 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 120 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 120 241 (accept_3_3 53 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 120 241 (Polychromatic418967fa.accept_16_4_8_1_1_5257 52 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 120 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 241 (accept_3_3 50 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 241
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 48 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 120 241 (accept_3_3 47 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 120 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 120 241 (Polychromatic418967fa.accept_19_7_6_13_1_6322 45 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 241 (accept_3_3 44 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 241 (Polychromatic418967fa.accept_13_4_3_7_1_2515 43 120
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 120 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 120 241 (accept_3_3 41 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 120 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 120 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 241 (accept_3_3 38 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 241
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 120 241 (accept_3_3 35 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 120 241 (Polychromatic418967fa.accept_13_8_3_7_1_2455 34 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 120 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 241 (accept_3_3 32 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 120 241 (accept_3_3 29 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 120 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 120 241 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 241 (accept_3_3 26 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 120 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 120 241 (accept_3_3 23 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 120 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 120 241 (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 241 (accept_3_3 20 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 120 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 120 241 (accept_3_3 17 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 120 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 120 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 241 (accept_3_3 14 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 120 241 (accept_3_3 11 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 120 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 120 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 241 (accept_3_3 8 120 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 241 (Polychromatic418967fa.accept_16_7_8_1_1_3061 7 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 120 241 (accept_3_3 5 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  120 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 120 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 120 241 (Polychromatic418967fa.accept_18_3_12_7_1_6728 3 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 241 (accept_3_3 2 120 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 241 (allA_of_3_1 119 119 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 118 241
  (allA_succ_of_accept 117 118 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 117 118 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 118 241 (accept_3_3 116 118 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 115 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 118 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 114 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 118 241 (accept_3_3 113 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 118 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 112 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 118 241 (accept_3_3 110 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 118 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 109 118
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 118 241
  (Polychromatic418967fa.accept_11_9_8_10_1_934 108 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 118 241 (accept_3_3 107 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 118 241 (Polychromatic418967fa.accept_17_4_16_3_1_4620 106 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 118 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 118 241 (accept_3_3 104 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 118
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 118 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 102 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 118 241 (accept_3_3 101 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 118 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 100 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 118 241 (accept_3_3 98 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 118 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 97 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 118 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 96 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 118 241 (accept_3_3 95 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 118 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 118 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 118 241 (accept_3_3 92 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 118 241
  (Polychromatic418967fa.accept_19_14_4_13_1_7779 90 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 118 241 (accept_3_3 89 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 118 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 118 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 118 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 118 241 (accept_3_3 86 118 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 118 241 (Polychromatic418967fa.accept_9_4_1_7_1_293
  85 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 118 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 118 241 (accept_3_3 83 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 118 241 (Polychromatic418967fa.accept_16_2_6_1_1_2069 82 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 118 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 118 241 (accept_3_3 80 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 118 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 78 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 118 241 (accept_3_3 77 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 118 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 241 (accept_3_3 74 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 73 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 118 241 (accept_3_3 71 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 118 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 70 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 118 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 241 (accept_3_3 68 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 241 (accept_3_3 65 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 64 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 241 (accept_3_3 62 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 241 (Polychromatic418967fa.accept_23_15_3_11_1_6268 61 118 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 241 (accept_3_3 59 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 241 (accept_3_3 56 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 241
  (Polychromatic418967fa.accept_23_8_3_11_1_14511 54 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 118 241 (accept_3_3 53 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 118 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 118 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 118 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 241 (accept_3_3 50 118 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 241 (Polychromatic418967fa.accept_9_4_1_7_1_293
  49 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 241 (accept_3_3 47 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 241 (accept_3_3 44 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 241 (accept_3_3 41 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 241 (accept_3_3 38 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 241
  (Polychromatic418967fa.accept_19_17_4_13_1_4828 36 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 118 241 (accept_3_3 35 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 118 241 (Polychromatic418967fa.accept_13_8_1_7_1_2505 34 118 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 118 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 118 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 241 (accept_3_3 32 118 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 241 (accept_3_3 29 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 241 (accept_3_3 26 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 241 (accept_3_3 23 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 241 (accept_3_3 20 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 241 (accept_3_3 17 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 241 (accept_3_3 14 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 241 (accept_3_3 11 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 241 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 241 (accept_3_3 8 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 241 (accept_3_3 5 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 118 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 241 (accept_3_3 2 118 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 241 (Polychromatic418967fa.accept_21_1_13_10_1_11627 1 118 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 241 (allA_succ_of_accept 116 117 241 (accept_3_3 116 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 241 (Polychromatic418967fa.accept_25_15_17_16_1_14510 115 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 241 (Polychromatic418967fa.accept_7_2_5_3_1_98
  114 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 241 (accept_3_3
  113 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 241
  (Polychromatic418967fa.accept_6_4_3_1_1_57 112 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 117 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 111 117 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 241 (accept_3_3 110 117 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 117 241 (Polychromatic418967fa.accept_15_4_12_1_1_1081 109 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 241
  (Polychromatic418967fa.accept_8_4_5_1_1_299 108 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 117 241 (accept_3_3 107 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 106 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 117 241 (Polychromatic418967fa.accept_16_9_5_1_1_1259 105 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 241 (accept_3_3 104 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 241 (Polychromatic418967fa.accept_15_13_12_1_1_1841 103
  117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 241
  (Polychromatic418967fa.accept_11_3_7_10_1_180 102 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 117 241 (accept_3_3 101 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 117 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 99 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 241 (accept_3_3 98 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 241 (Polychromatic418967fa.accept_17_12_15_3_1_7168 97 117 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 241
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 96 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 117 241 (accept_3_3 95 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 117 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 241 (accept_3_3 92 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 91 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 241
  (Polychromatic418967fa.accept_20_10_17_1_1_8852 90 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 241 (accept_3_3 89 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 117 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 87 117
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 241 (accept_3_3 86 117
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 85 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 117 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 117 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 241 (accept_3_3 83 117 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 241
  (Polychromatic418967fa.accept_25_6_17_16_1_14509 81 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 117 241 (accept_3_3 80 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 117 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 117 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 241 (accept_3_3 77 117 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76
  117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 117 241 (accept_3_3 74 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 117 241 (Polychromatic418967fa.accept_15_13_12_1_1_1841 73 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 117 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 241 (accept_3_3 71 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 241
  (Polychromatic418967fa.accept_11_3_7_10_1_180 69 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 117 241 (accept_3_3 68 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 117 241 (Polychromatic418967fa.accept_19_10_3_13_1_6284 67 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 117 241 (Polychromatic418967fa.accept_10_6_7_1_1_1297 66 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 241 (accept_3_3 65 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 117 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 117 241 (accept_3_3 62 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 117 241 (Polychromatic418967fa.accept_16_13_5_1_1_3017 61 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 117 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 241 (accept_3_3 59 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 117 241 (accept_3_3 56 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 117 241 (Polychromatic418967fa.accept_22_11_7_21_1_9879 55 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 117 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 241 (accept_3_3 53 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 117 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 117 241 (accept_3_3 50 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 117 241 (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 117 241 (Polychromatic418967fa.accept_17_14_15_3_1_4618 48 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 241 (accept_3_3 47 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 117 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 241
  (Polychromatic418967fa.accept_16_13_5_1_1_3017 45 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 117 241 (accept_3_3 44 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 117 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 117 241 (Polychromatic418967fa.accept_18_6_9_7_1_2905 42 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 241 (accept_3_3 41 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 117 241 (accept_3_3 38 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 117 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 117 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 241 (accept_3_3 35 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 241
  (Polychromatic418967fa.accept_22_11_7_21_1_9879 33 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 241 (accept_3_3 32 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 241 (Polychromatic418967fa.accept_16_15_5_1_1_7724 31 117 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 117 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 241 (accept_3_3 29 117 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 117 241 (accept_3_3 26 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 117 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 117 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 241 (accept_3_3 23 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 117 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 241
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 21 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 117 241 (accept_3_3 20 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 117 241 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 117 241 (Polychromatic418967fa.accept_17_1_15_3_1_1501 18 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 241 (accept_3_3 17 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 241 (accept_3_3 14 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 117 241 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 241 (accept_3_3 11 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 241 (accept_3_3 8 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  117 241 (Polychromatic418967fa.accept_19_7_3_13_1_3492 7 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 241 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 241 (accept_3_3 5 117 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 241
  (Polychromatic418967fa.accept_11_3_7_10_1_180 3 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 241 (accept_3_3 2 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 117 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 241 (allA_of_3_1 116 116 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 241
  (allA_succ_of_accept 114 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 114 115 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 241 (accept_3_3 113 115 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 115 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 112 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 241
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 111 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 115 241 (accept_3_3 110 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 115 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 109 115 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 115 241
  (Polychromatic418967fa.accept_13_4_11_7_1_558 108 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 115 241 (accept_3_3 107 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 106 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 115 241 (Polychromatic418967fa.accept_11_6_5_10_1_2724 105 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 115 241 (accept_3_3 104 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 115 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 103 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 115 241 (accept_3_3 101 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 115 241 (Polychromatic418967fa.accept_13_9_11_7_1_1077 100 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 115 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 99 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 115 241 (accept_3_3 98 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 115 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 97 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 115 241
  (Polychromatic418967fa.accept_10_6_5_1_1_482 96 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 115 241 (accept_3_3 95 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 115 241 (Polychromatic418967fa.accept_16_13_3_1_1_2100 93 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 115 241 (accept_3_3 92 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 115 241 (Polychromatic418967fa.accept_26_13_11_7_1_14508 91
  115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 115 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 90 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 115 241 (accept_3_3 89 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 115 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 88 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 115 241 (Polychromatic418967fa.accept_13_9_11_7_1_1077 87 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 115 241 (accept_3_3 86 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 115 241 (Polychromatic418967fa.accept_20_5_15_1_1_7278 85 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 115 241
  (Polychromatic418967fa.accept_10_4_5_1_1_497 84 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 115 241 (accept_3_3 83 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 115 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 81 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 115 241 (accept_3_3 80 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 115 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 79 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 115 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 115 241 (accept_3_3 77 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 115 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 76 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 115 241 (Polychromatic418967fa.accept_19_18_1_13_1_14507 75 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 115 241 (accept_3_3 74 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 73 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 241
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 72 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 115 241 (accept_3_3 71 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 115 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 241 (accept_3_3 68 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 115 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 67 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 115 241 (accept_3_3 65 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 115 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 64 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 115 241 (Polychromatic418967fa.accept_27_9_7_25_1_2944 63 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 241 (accept_3_3 62 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 241 (Polychromatic418967fa.accept_11_6_5_10_1_2724 61 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 241
  (Polychromatic418967fa.accept_22_16_5_21_1_8266 60 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 115 241 (accept_3_3 59 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 115 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 241 (Polychromatic418967fa.accept_13_5_11_7_1_559 57 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 241 (accept_3_3 56 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 115 241
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 55 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 115 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 241 (accept_3_3 53 115 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 115 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 52 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 241
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 115 241 (accept_3_3 50 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 115 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 115 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 48 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 241 (accept_3_3 47 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2
  46 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 241
  (Polychromatic418967fa.accept_16_13_3_1_1_2100 45 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 241 (accept_3_3 44 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 241 (Polychromatic418967fa.accept_13_4_11_7_1_558 43 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 115 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 241 (accept_3_3 41 115 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 241 (Polychromatic418967fa.accept_13_1_11_7_1_1704 40 115 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 241
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 241 (accept_3_3 38 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 37 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 241 (accept_3_3 35 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 115 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 241
  (Polychromatic418967fa.accept_17_16_13_3_1_4677 33 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 115 241 (accept_3_3 32 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 115 241 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 115 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 115 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 241 (accept_3_3 29 115 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 241
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 28 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 115 241 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 115 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 241 (accept_3_3 26 115 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 115 241 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 241
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 241 (accept_3_3 23 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 241 (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 241 (accept_3_3 20 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 241 (accept_3_3 17 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 241 (accept_3_3 14 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 241
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 115 241 (accept_3_3 11 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 115 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 115 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 115 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 241 (accept_3_3 8 115 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836
  7 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 241 (accept_3_3 5 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 115 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 241 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 241 (accept_3_3 2 115 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 241 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 115
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 241 (allA_succ_of_accept 113 114 241 (accept_3_3 113 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 114 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 112 114 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 114 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 114
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 241 (accept_3_3 110 114
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 114 241
  (Polychromatic418967fa.accept_9_1_6_7_1_285 109 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 114 241 (Polychromatic418967fa.accept_13_4_10_7_1_1701 108 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 241 (accept_3_3 107 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 106 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 241
  (Polychromatic418967fa.accept_10_5_4_1_1_842 105 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 114 241 (accept_3_3 104 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 114 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 114 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 102 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 241 (accept_3_3 101 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 100 114
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 99 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 114 241 (accept_3_3 98 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 114 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 114 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 241 (accept_3_3 95 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 94 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 114 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 93 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 114 241 (accept_3_3 92 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 114 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 114 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 114 241 (accept_3_3 89 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 241 (Polychromatic418967fa.accept_23_19_22_11_1_6104 88 114 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 87 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 114 241 (accept_3_3 86 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 114 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 114 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 84 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 114 241 (accept_3_3 83 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 114 241
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 81 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 114 241 (accept_3_3 80 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 114 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 114 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 114 241 (accept_3_3 77 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 114 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 114 241 (accept_3_3 74 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 114 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 114 241 (Polychromatic418967fa.accept_23_3_22_11_1_2978 72 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 114 241 (accept_3_3 71 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 241 (Polychromatic418967fa.accept_15_10_9_1_1_3688 70 114
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 114 241 (accept_3_3 68 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 114 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 114 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 114 241 (accept_3_3 65 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 114 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 114 241 (accept_3_3 62 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 114 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 114 241 (Polychromatic418967fa.accept_11_5_4_10_1_524 60 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 114 241 (accept_3_3 59 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 114 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 114 241 (accept_3_3 56 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 114 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 114 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 241 (accept_3_3 53 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 241 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 114 241 (accept_3_3 50 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 114 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 114 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 241 (accept_3_3 47 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 241
  (Polychromatic418967fa.accept_10_5_4_1_1_842 45 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 114 241 (accept_3_3 44 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 114 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 114 241 (Polychromatic418967fa.accept_13_3_10_7_1_1061 42 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 241 (accept_3_3 41 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 114 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 114 241 (accept_3_3 38 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 114 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 114 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 241 (accept_3_3 35 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 114 241 (accept_3_3 32 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 114 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 114 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 241 (accept_3_3 29 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 114 241 (accept_3_3 26 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 114 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 114 241 (Polychromatic418967fa.accept_17_7_12_3_1_4693 24 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 241 (accept_3_3 23 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 114 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 114 241 (accept_3_3 20 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 114 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 114 241 (Polychromatic418967fa.accept_21_18_9_10_1_2571 18 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 241 (accept_3_3 17 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 241 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 114
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 114 241 (accept_3_3 14 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 114 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 114 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 241 (accept_3_3 11 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 241
  (Polychromatic418967fa.accept_16_9_2_1_1_3077 9 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 114 241 (accept_3_3 8 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  114 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 114 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 241 (accept_3_3 5 114 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 114 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 114 241 (accept_3_3 2 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  114 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 114 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 114
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 241 (allA_of_3_1 113 113 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 241
  (allA_succ_of_accept 111 112 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 112 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 112 241 (accept_3_3 110 112 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 109 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 112 241
  (Polychromatic418967fa.accept_21_3_7_10_1_7002 108 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 112 241 (accept_3_3 107 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 112 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 106 112 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 112 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 112 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 112 241 (accept_3_3 104 112 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 112 241 (Polychromatic418967fa.accept_10_3_2_1_1_839
  103 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 112 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 102 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 112 241 (accept_3_3 101 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 100 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 112 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 112 241 (accept_3_3 98 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 112 241 (Polychromatic418967fa.accept_21_13_7_10_1_8599 97 112 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 112 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 96 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 112 241 (accept_3_3 95 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 112 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 94 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 112 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 112 241 (accept_3_3 92 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 112 241
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 90 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 112 241 (accept_3_3 89 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 112 241 (Polychromatic418967fa.accept_13_10_8_7_1_1074 88 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 112 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 112 241 (accept_3_3 86 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 112 241 (Polychromatic418967fa.accept_15_10_7_1_1_3686 85 112 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 112 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 112 241 (accept_3_3 83 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 112 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 112 241 (accept_3_3 80 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 112 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 79 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 112 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 112 241 (accept_3_3 77 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 112 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 76 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 112 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 112 241 (accept_3_3 74 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 112 241
  (Polychromatic418967fa.accept_19_15_17_13_1_4901 72 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 112 241 (accept_3_3 71 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 112 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 112 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 112 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 112 241 (accept_3_3 68 112 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 112 241
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 67 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 112 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 112 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 241 (accept_3_3 65 112 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 112 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 63
  112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 112 241 (accept_3_3 62
  112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 112 241
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 61 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 112 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 112 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 241 (accept_3_3 59 112 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 112 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 241 (accept_3_3 56 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 241 (Polychromatic418967fa.accept_13_2_8_7_1_2424 54 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 241 (accept_3_3 53 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 241 (Polychromatic418967fa.accept_18_16_4_7_1_2927 52 112
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 241 (accept_3_3 50 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 241 (accept_3_3 47 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 241 (accept_3_3 44 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 241 (accept_3_3 41 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 241 (Polychromatic418967fa.accept_13_1_8_7_1_1088 40 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 241 (accept_3_3 38 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 241 (accept_3_3 35 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 241 (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 112
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 241 (accept_3_3 32 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 241 (Polychromatic418967fa.accept_18_13_4_7_1_4086 31 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 241 (accept_3_3 29 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 241 (accept_3_3 26 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 241 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 241 (accept_3_3 23 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 112 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 241 (accept_3_3 20 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 241 (Polychromatic418967fa.accept_19_18_17_13_1_6296 18 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 241 (accept_3_3 17 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 112
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 241 (accept_3_3 14 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 112 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 241 (accept_3_3 11 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 241 (accept_3_3 8 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 241 (Polychromatic418967fa.accept_17_7_10_3_1_1421 7 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 241 (accept_3_3 5 112 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 241 (Polychromatic418967fa.accept_19_4_17_13_1_4929 4 112 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 241 (accept_3_3 2 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 241 (allA_succ_of_accept 110 111 241 (accept_3_3 110 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 109 111 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 108 111
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 241 (accept_3_3 107 111
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 106 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 111 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 105 111 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 241 (accept_3_3 104 111 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 111 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 103 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 111 241 (accept_3_3 101 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 111 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 111 241 (Polychromatic418967fa.accept_15_9_6_1_1_493 99 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 241 (accept_3_3 98 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 97 111
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 96 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 111 241 (accept_3_3 95 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 111 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 111 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 241 (accept_3_3 92 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 91 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 90 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 111 241 (accept_3_3 89 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 111 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 111 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 241 (accept_3_3 86 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 85 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 241
  (Polychromatic418967fa.accept_15_9_6_1_1_493 84 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 241 (accept_3_3 83 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 111 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 111 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 241 (accept_3_3 80 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 241 (accept_3_3 77 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 75 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 241 (accept_3_3 74 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 111 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 111 241 (accept_3_3 71 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 111 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 241 (accept_3_3 68 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 241 (accept_3_3 65 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 241 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 241 (accept_3_3 62 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 241 (Polychromatic418967fa.accept_17_10_9_3_1_7144 61 111
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 241 (accept_3_3 59 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 57 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 241 (accept_3_3 56 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 111 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 241 (accept_3_3 53 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 241 (accept_3_3 50 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 241
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 241 (accept_3_3 47 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 241 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 241 (accept_3_3 44 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 241 (Polychromatic418967fa.accept_16_11_15_1_1_2074 43 111
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 241 (accept_3_3 41 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 241 (accept_3_3 38 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 241
  (Polychromatic418967fa.accept_19_17_16_13_1_4900 36 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 241 (accept_3_3 35 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 111 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 111 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 241 (accept_3_3 32 111 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 241 (Polychromatic418967fa.accept_9_4_3_7_1_296
  31 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 241 (accept_3_3 29 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 241 (Polychromatic418967fa.accept_16_11_15_1_1_2074 27 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 241 (accept_3_3 26 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 111 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 241 (accept_3_3 23 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 241 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 241 (accept_3_3 20 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 111 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 241 (accept_3_3 17 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 241 (accept_3_3 14 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 241
  (Polychromatic418967fa.accept_18_12_3_7_1_5373 12 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 241 (accept_3_3 11 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 241 (accept_3_3 8 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 241 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 241 (accept_3_3 5 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 241 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 241 (accept_3_3 2 111 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 111 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 241 (allA_of_3_1 110 110 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 241
  (allA_succ_of_accept 108 109 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 108 109 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 241 (accept_3_3 107 109 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 109 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 106 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 105 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 241 (accept_3_3 104 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 103 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 102 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 241 (accept_3_3 101 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 100 109
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 99 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 241 (accept_3_3 98 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 241 (accept_3_3 95 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 93 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 241 (accept_3_3 92 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 91 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 241 (accept_3_3 89 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 241 (Polychromatic418967fa.accept_10_8_9_1_1_189 88 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 87 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 241 (accept_3_3 86 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 241 (accept_3_3 83 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 241 (Polychromatic418967fa.accept_10_2_9_1_1_185 82 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 241
  (Polychromatic418967fa.accept_19_5_14_13_1_7816 81 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 109 241 (accept_3_3 80 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 109 241 (Polychromatic418967fa.accept_21_16_4_10_1_14506 79 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 109 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 78
  109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 241 (accept_3_3 77
  109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 76 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 109 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 109 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 109 241 (accept_3_3 74 109 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 109 241 (Polychromatic418967fa.accept_16_9_13_1_1_3069 73 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 241
  (Polychromatic418967fa.accept_10_2_9_1_1_185 72 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 109 241 (accept_3_3 71 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 109 241 (Polychromatic418967fa.accept_18_16_1_7_1_4083 70 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 109 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 241 (accept_3_3 68 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 109 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 109 241 (accept_3_3 65 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 109 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 109 241 (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 241 (accept_3_3 62 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 241 (Polychromatic418967fa.accept_17_10_7_3_1_727 61 109
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 241
  (Polychromatic418967fa.accept_8_4_5_1_1_299 60 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 109 241 (accept_3_3 59 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 109 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 241 (accept_3_3 56 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 241
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 241 (accept_3_3 53 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 241 (accept_3_3 50 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 241 (accept_3_3 47 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 241 (Polychromatic418967fa.accept_16_14_13_1_1_5278 46 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 241 (accept_3_3 44 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 109 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 241 (accept_3_3 41 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 241 (accept_3_3 38 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 241 (Polychromatic418967fa.accept_13_11_5_7_1_2420 37 109 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 241 (accept_3_3 35 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 241 (accept_3_3 32 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 241 (accept_3_3 29 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 241 (accept_3_3 26 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 241 (accept_3_3 23 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 241 (accept_3_3 20 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 241 (Polychromatic418967fa.accept_16_3_13_1_1_1206 19 109 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 241
  (Polychromatic418967fa.accept_10_8_9_1_1_189 18 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 241 (accept_3_3 17 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 241 (Polychromatic418967fa.accept_17_16_7_3_1_4644 16 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 241 (accept_3_3 14 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 241
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 241 (accept_3_3 11 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 241 (Polychromatic418967fa.accept_17_10_7_3_1_727 10 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 241 (Polychromatic418967fa.accept_16_9_13_1_1_3069 9 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 241 (accept_3_3 8 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 109
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 241 (accept_3_3 5 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 109 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 241 (accept_3_3 2 109 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 109 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 241 (allA_succ_of_accept 107 108 241 (accept_3_3 107 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 108 241 (Polychromatic418967fa.accept_21_1_3_10_1_5401 106 108 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 241
  (Polychromatic418967fa.accept_14_7_10_3_1_1034 105 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 108 241 (accept_3_3 104 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 108 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 103 108 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 108 241 (Polychromatic418967fa.accept_13_11_4_7_1_2419 102
  108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 241 (accept_3_3 101
  108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 241
  (Polychromatic418967fa.accept_11_1_9_10_1_184 100 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 108 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 99 108 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 108 241 (accept_3_3 98 108 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 108 241 (Polychromatic418967fa.accept_13_6_4_7_1_2464 97 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 108 241
  (Polychromatic418967fa.accept_11_8_9_10_1_503 96 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 108 241 (accept_3_3 95 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 108 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 94 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 108 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 93 108 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 108 241 (accept_3_3 92 108 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 108 241 (Polychromatic418967fa.accept_14_7_10_3_1_1034 91 108 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 108 241
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 90 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 108 241 (accept_3_3 89 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 108 241 (Polychromatic418967fa.accept_13_10_4_7_1_2465 88 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 108 241 (Polychromatic418967fa.accept_13_9_4_7_1_1694 87 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 108 241 (accept_3_3 86 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 108 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 85 108 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 108 241
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 84 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 108 241 (accept_3_3 83 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 108 241 (Polychromatic418967fa.accept_16_2_12_1_1_3086 82 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 108 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 81 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 108 241 (accept_3_3 80 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 108 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 79 108
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 108 241
  (Polychromatic418967fa.accept_11_1_9_10_1_184 78 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 108 241 (accept_3_3 77 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 108 241 (Polychromatic418967fa.accept_13_11_4_7_1_2419 76 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 108 241 (Polychromatic418967fa.accept_13_10_4_7_1_2465 75 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 241 (accept_3_3 74 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 73 108
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 108 241
  (Polychromatic418967fa.accept_16_8_12_1_1_7720 72 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 108 241 (accept_3_3 71 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 108 241 (Polychromatic418967fa.accept_21_7_3_10_1_13044 70 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 108 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 108 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 241 (accept_3_3 68 108 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 67 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 108 241
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 66 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 108 241 (accept_3_3 65 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 108 241 (Polychromatic418967fa.accept_13_12_4_7_1_2520 64 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 108 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 241 (accept_3_3 62 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 108 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 108 241
  (Polychromatic418967fa.accept_17_9_6_3_1_2398 60 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 108 241 (accept_3_3 59 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 108 241 (Polychromatic418967fa.accept_13_6_4_7_1_2464 58 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 108 241 (Polychromatic418967fa.accept_21_15_3_10_1_8533 57 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 241 (accept_3_3 56 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 55 108
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 241
  (Polychromatic418967fa.accept_21_12_3_10_1_8575 54 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 108 241 (accept_3_3 53 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 108 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 52 108 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 241 (Polychromatic418967fa.accept_13_12_4_7_1_2520 51 108
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 241 (accept_3_3 50 108
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 241
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 108 241 (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 108 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 241 (accept_3_3 47 108 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 108 241 (Polychromatic418967fa.accept_25_21_8_16_1_12812 46 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 241
  (Polychromatic418967fa.accept_8_5_4_1_1_111 45 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 108 241 (accept_3_3 44 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 108 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 108 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 241 (accept_3_3 41 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 241 (Polychromatic418967fa.accept_16_8_12_1_1_7720 40 108
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 241
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 108 241 (accept_3_3 38 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 108 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 108 241 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 241 (accept_3_3 35 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 34 108
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 241
  (Polychromatic418967fa.accept_10_3_8_1_1_182 33 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 241 (accept_3_3 32 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 108 241 (Polychromatic418967fa.accept_17_14_6_3_1_2362 31 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 108 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 241 (accept_3_3 29 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 241 (Polychromatic418967fa.accept_15_13_3_1_1_3740 28 108
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 241
  (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 108 241 (accept_3_3 26 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 108 241 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 108 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 241 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 108
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 241 (accept_3_3 23 108
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 241
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 22 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 108 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 108 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 241 (accept_3_3 20 108 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 108 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 241
  (Polychromatic418967fa.accept_16_2_12_1_1_3086 18 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 108 241 (accept_3_3 17 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 108 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 108 241 (Polychromatic418967fa.accept_21_15_3_10_1_8533 15 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 241 (accept_3_3 14 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 108 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 241
  (Polychromatic418967fa.accept_11_1_9_10_1_184 12 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 108 241 (accept_3_3 11 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 108 241 (Polychromatic418967fa.accept_13_10_4_7_1_2465 10 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 108 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 108 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 241 (accept_3_3 8 108 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 241 (Polychromatic418967fa.accept_14_7_10_3_1_1034 7 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 241
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 6 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 108 241 (accept_3_3 5 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  108 241 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 108 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 108 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 108 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 241 (accept_3_3 2 108 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 108 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 241 (allA_of_3_1 107 107 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 241
  (allA_succ_of_accept 105 106 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 106 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 241 (accept_3_3 104 106 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 102 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 106 241 (accept_3_3 101 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 106 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 241 (accept_3_3 98 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 97 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 96 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 241 (accept_3_3 95 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 241 (Polychromatic418967fa.accept_18_4_16_7_1_1873 94 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 241 (accept_3_3 92 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 241
  (Polychromatic418967fa.accept_25_15_6_16_1_14505 90 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 106 241 (accept_3_3 89 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 106 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 106 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 106 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 241 (accept_3_3 86 106 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 241 (Polychromatic418967fa.accept_10_5_6_1_1_836
  85 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 241
  (Polychromatic418967fa.accept_17_16_4_3_1_3429 84 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 241 (accept_3_3 83 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 241 (accept_3_3 80 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 241
  (Polychromatic418967fa.accept_19_2_11_13_1_9180 78 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 106 241 (accept_3_3 77 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 106 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 76 106 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 106 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 241 (accept_3_3 74 106 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 241 (Polychromatic418967fa.accept_13_8_2_7_1_2452
  73 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 241 (accept_3_3 71 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 241 (Polychromatic418967fa.accept_13_5_2_7_1_2414 70 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 241 (accept_3_3 68 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 241
  (Polychromatic418967fa.accept_21_3_1_10_1_10008 66 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 106 241 (accept_3_3 65 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 106 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 106 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 106 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 241 (accept_3_3 62 106 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 241 (Polychromatic418967fa.accept_7_5_1_3_1_103
  61 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 241 (accept_3_3 59 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 241 (accept_3_3 56 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 241 (accept_3_3 53 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 241 (accept_3_3 50 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 241 (Polychromatic418967fa.accept_21_7_1_10_1_8571 49 106 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 241
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 48 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 241 (accept_3_3 47 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 241 (accept_3_3 44 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 241
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 241 (accept_3_3 41 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 241 (accept_3_3 38 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 241
  (Polychromatic418967fa.accept_11_3_7_10_1_180 36 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 241 (accept_3_3 35 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 241 (Polychromatic418967fa.accept_13_8_2_7_1_2452 34 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 241 (accept_3_3 32 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 241 (accept_3_3 29 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 241 (accept_3_3 26 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 241
  (Polychromatic418967fa.accept_17_7_4_3_1_3456 24 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 241 (accept_3_3 23 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 241 (accept_3_3 20 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 241 (accept_3_3 17 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 241 (accept_3_3 14 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 241 (Polychromatic418967fa.accept_17_13_4_3_1_1446 13 106 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 241 (accept_3_3 11 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 241 (Polychromatic418967fa.accept_22_10_18_21_1_8227 10 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 241 (accept_3_3 8 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 241
  (Polychromatic418967fa.accept_19_6_11_13_1_4842 6 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 241 (accept_3_3 5 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 106 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 241 (accept_3_3 2 106 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 241 (Polychromatic418967fa.accept_18_1_16_7_1_2897 1 106 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 241 (allA_succ_of_accept 104 105 241 (accept_3_3 104 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 103 105 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 102 105
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 241 (accept_3_3 101 105
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 241
  (Polychromatic418967fa.accept_6_4_3_1_1_57 100 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 99 105 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 241 (accept_3_3 98 105 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 105 241 (Polychromatic418967fa.accept_13_6_1_7_1_1690 97 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 241
  (Polychromatic418967fa.accept_10_6_5_1_1_482 96 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 105 241 (accept_3_3 95 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 105 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 241 (accept_3_3 92 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 241
  (Polychromatic418967fa.accept_16_10_9_1_1_9973 90 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 105 241 (accept_3_3 89 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 105 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 87 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 241 (accept_3_3 86 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 85 105 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 105 241 (accept_3_3 83 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 105 241 (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 241 (accept_3_3 80 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 79 105
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 241
  (Polychromatic418967fa.accept_19_2_10_13_1_9147 78 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 105 241 (accept_3_3 77 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 105 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 105 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 105 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 241 (accept_3_3 74 105 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 241 (Polychromatic418967fa.accept_9_1_6_7_1_285
  73 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 241
  (Polychromatic418967fa.accept_16_8_9_1_1_7753 72 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 105 241 (accept_3_3 71 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 105 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 241 (accept_3_3 68 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 105 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 241 (accept_3_3 65 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 105 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 63 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 241 (accept_3_3 62 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 241 (Polychromatic418967fa.accept_16_13_9_1_1_3022 61 105
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 241
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 60 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 105 241 (accept_3_3 59 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 241 (accept_3_3 56 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 241
  (Polychromatic418967fa.accept_10_4_5_1_1_497 54 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 241 (accept_3_3 53 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 241 (accept_3_3 50 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 105 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 241 (accept_3_3 47 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 241 (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 241 (accept_3_3 44 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 241 (Polychromatic418967fa.accept_19_5_10_13_1_4883 43 105
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 241
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 42 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 241 (accept_3_3 41 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 241 (accept_3_3 38 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 241
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 241 (accept_3_3 35 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 241 (Polychromatic418967fa.accept_23_10_13_11_1_14504 33 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 241 (accept_3_3 32 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 105 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 241 (accept_3_3 29 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 241 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 241 (accept_3_3 26 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 241 (Polychromatic418967fa.accept_14_11_7_3_1_3416 25 105
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 241
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 241 (accept_3_3 23 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 241 (accept_3_3 20 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 241
  (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 241 (accept_3_3 17 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 241 (accept_3_3 14 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 105 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 241 (accept_3_3 11 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 241 (accept_3_3 8 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 241 (Polychromatic418967fa.accept_22_7_17_21_1_14503 7 105 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 241
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 241 (accept_3_3 5 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 241 (accept_3_3 2 105 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 105 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 241 (allA_of_3_1 104 104 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 241
  (allA_succ_of_accept 102 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 103 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 241 (accept_3_3 101 103 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 99 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 241 (accept_3_3 98 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 241 (Polychromatic418967fa.accept_13_6_12_7_1_5131 97 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 241 (accept_3_3 95 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 241 (accept_3_3 92 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 241 (accept_3_3 89 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 88 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 87 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 241 (accept_3_3 86 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 241 (accept_3_3 83 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 241
  (Polychromatic418967fa.accept_19_5_8_13_1_9161 81 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 241 (accept_3_3 80 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 241 (accept_3_3 77 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 241 (Polychromatic418967fa.accept_13_11_12_7_1_2443 76 103 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 241 (accept_3_3 74 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 241 (accept_3_3 71 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 69 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 241 (accept_3_3 68 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 241 (Polychromatic418967fa.accept_21_4_19_10_1_8531 67 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 241 (accept_3_3 65 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 241
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 63 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 103 241 (accept_3_3 62 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 103 241 (Polychromatic418967fa.accept_19_4_8_13_1_7802 61 103 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 103 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 241 (accept_3_3 59 103 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58
  103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 241 (accept_3_3 56 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 241 (accept_3_3 53 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 52 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 241 (accept_3_3 50 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 241 (Polychromatic418967fa.accept_11_5_4_10_1_524 49 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 241 (accept_3_3 47 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 241
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 241 (accept_3_3 44 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 241 (accept_3_3 41 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 241 (Polychromatic418967fa.accept_14_12_5_3_1_1011 40 103 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 241 (accept_3_3 38 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 241 (accept_3_3 35 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 241 (accept_3_3 32 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 241 (Polychromatic418967fa.accept_13_5_12_7_1_1080 31 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 241 (accept_3_3 29 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 241
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 241 (accept_3_3 26 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 241 (accept_3_3 23 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 241 (accept_3_3 20 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 241 (accept_3_3 17 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 241 (accept_3_3 14 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 241 (Polychromatic418967fa.accept_20_13_3_1_1_3065 13 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 241 (accept_3_3 11 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 241 (accept_3_3 8 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 241 (Polychromatic418967fa.accept_21_7_19_10_1_8567 7 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 241 (accept_3_3 5 103 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 241 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 103 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 241 (accept_3_3 2 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 103 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 241 (allA_succ_of_accept 101 102 241 (accept_3_3 101 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 102 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 100 102 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 102 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 241 (accept_3_3 98 102 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 241 (Polychromatic418967fa.accept_7_6_4_3_1_266
  97 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 96 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 241 (accept_3_3 95 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 102 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 94 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 93 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 241 (accept_3_3 92 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 102 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 90 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 102 241 (accept_3_3 89 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 102 241 (Polychromatic418967fa.accept_15_13_12_1_1_1841 88 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 241 (accept_3_3 86 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 241
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 84 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 102 241 (accept_3_3 83 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 102 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 102 241 (Polychromatic418967fa.accept_13_3_11_7_1_2488 81 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 241 (accept_3_3 80 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 102 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 78 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 102 241 (accept_3_3 77 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 102 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 241 (accept_3_3 74 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 241
  (Polychromatic418967fa.accept_19_15_7_13_1_11844 72 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 102 241 (accept_3_3 71 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 102 241 (Polychromatic418967fa.accept_13_5_11_7_1_559 70 102 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 102 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 102 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 241 (accept_3_3 68 102 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67
  102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 66 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 102 241 (accept_3_3 65 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 102 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 241 (accept_3_3 62 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 241 (Polychromatic418967fa.accept_13_9_11_7_1_1077 61 102 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 241 (accept_3_3 59 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 102 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 241 (accept_3_3 56 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 241
  (Polychromatic418967fa.accept_22_10_14_21_1_8328 54 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 241 (accept_3_3 53 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 102 241 (Polychromatic418967fa.accept_22_8_14_21_1_11456 52 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51
  102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 241 (accept_3_3 50
  102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 241
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 102 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 102 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 102 241 (accept_3_3 47 102 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 102 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 241
  (Polychromatic418967fa.accept_21_3_18_10_1_10020 45 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 102 241 (accept_3_3 44 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 102 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 102 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 102 241 (accept_3_3 41 102 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 241 (Polychromatic418967fa.accept_9_4_3_7_1_296
  40 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 102 241 (accept_3_3 38 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 102 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 102 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 241 (accept_3_3 35 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 102 241 (accept_3_3 32 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 102 241 (Polychromatic418967fa.accept_13_4_11_7_1_558 30 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 241 (accept_3_3 29 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 102 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 102 241 (accept_3_3 26 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 102 241 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 102 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 241 (accept_3_3 23 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 241
  (Polychromatic418967fa.accept_14_7_4_3_1_488 21 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 102 241 (accept_3_3 20 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 102 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 241 (accept_3_3 17 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 102
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 102 241 (accept_3_3 14 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 102 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 102 241 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 241 (accept_3_3 11 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 102 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 241
  (Polychromatic418967fa.accept_10_9_2_1_1_840 9 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 102 241 (accept_3_3 8 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  102 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 102 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 241 (accept_3_3 5 102 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 102 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 102 241 (accept_3_3 2 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  102 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 102 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 102
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 241 (allA_of_3_1 101 101 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 241 (allA_succ_of_accept 99
  100 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 100 241 (accept_3_3 98 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 100 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 100 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 100 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 100 241 (accept_3_3 95 100 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 100 241 (Polychromatic418967fa.accept_9_4_1_7_1_293
  94 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 100 241 (accept_3_3 92 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 100 241 (Polychromatic418967fa.accept_21_7_16_10_1_1349 91 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 100 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 100 241 (accept_3_3 89 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 100 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 88 100 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 100 241 (accept_3_3 86 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 100 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 100 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 100 241 (accept_3_3 83 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 100 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 100 241 (accept_3_3 80 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 100 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 79 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 100 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 100 241 (accept_3_3 77 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 100 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 100 241 (accept_3_3 74 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 100 241 (Polychromatic418967fa.accept_13_8_9_7_1_530 73 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 100 241 (Polychromatic418967fa.accept_16_8_4_1_1_2102 72 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 100 241 (accept_3_3 71 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 100 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 100
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 100 241 (accept_3_3 68 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 100 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 100 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 100 241 (accept_3_3 65 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 100 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 100 241 (accept_3_3 62 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 100 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 100 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 100 241 (accept_3_3 59 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 100 241 (accept_3_3 56 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 100 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 100 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 100 241 (accept_3_3 53 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 100 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 52 100 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 100 241 (accept_3_3 50 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 100 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 100 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 241 (accept_3_3 47 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 100 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 46 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 100 241 (accept_3_3 44 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 100 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 100 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 100 241 (accept_3_3 41 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 100 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 100 241 (accept_3_3 38 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 100 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 100 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 241 (accept_3_3 35 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 100 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 100 241 (accept_3_3 32 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 100 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 100 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 241 (accept_3_3 29 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 241 (Polychromatic418967fa.accept_13_2_9_7_1_164 28 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 241 (accept_3_3 26 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 100 241 (Polychromatic418967fa.accept_21_4_16_10_1_10019 25 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 100 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 241 (accept_3_3 23 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 100 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 241 (accept_3_3 20 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 241 (Polychromatic418967fa.accept_17_1_15_3_1_1501 18 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 241 (accept_3_3 17 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 241 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 100
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 241 (accept_3_3 14 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 241 (accept_3_3 11 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 100 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 241 (accept_3_3 8 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 241 (accept_3_3 5 100 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 100 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 241 (accept_3_3 2 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 100 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  241 (allA_succ_of_accept 98 99 241 (accept_3_3 98 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 241 (Polychromatic418967fa.accept_15_7_9_1_1_473 97 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 241 (accept_3_3 95 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 241 (accept_3_3 92 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 241 (Polychromatic418967fa.accept_17_6_14_3_1_4678 91 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 241 (accept_3_3 89 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 241
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 87 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 241 (accept_3_3 86 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 85 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 241 (Polychromatic418967fa.accept_16_4_3_1_1_8843 84 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 241 (accept_3_3 83 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 241 (accept_3_3 80 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 241 (accept_3_3 77 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 241 (accept_3_3 74 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 241 (Polychromatic418967fa.accept_22_7_11_21_1_2095 73 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 241 (accept_3_3 71 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 69 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 241 (accept_3_3 68 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 241 (accept_3_3 65 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 241
  (Polychromatic418967fa.accept_19_6_4_13_1_2329 63 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 241 (accept_3_3 62 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 241 (accept_3_3 59 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 241 (accept_3_3 56 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 241 (accept_3_3 53 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 241 (accept_3_3 50 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 241 (Polychromatic418967fa.accept_13_10_8_7_1_1074 49 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 241 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 241 (accept_3_3 47 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 241
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 241 (accept_3_3 44 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 241 (Polychromatic418967fa.accept_21_1_15_10_1_11607 43 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 241 (accept_3_3 41 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 241 (accept_3_3 38 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 241 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 241 (accept_3_3 35 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 241 (accept_3_3 32 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 241 (Polychromatic418967fa.accept_26_5_21_7_1_10961 31 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 241 (accept_3_3 29 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 241
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 241 (accept_3_3 26 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 241 (Polychromatic418967fa.accept_18_6_9_7_1_2905 24 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 241 (accept_3_3 23 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 241 (accept_3_3 20 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 241 (accept_3_3 17 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 241
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 241 (accept_3_3 14 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 241 (Polychromatic418967fa.accept_16_13_3_1_1_2100 13 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 241 (accept_3_3 11 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 241 (accept_3_3 8 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  241 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 241 (accept_3_3 5 99 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 241 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3
  99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 241 (accept_3_3 2 99 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 241 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1
  99 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  241 (allA_of_3_1 98 98 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 241 (allA_succ_of_accept 96 97 241
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 96 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 241 (accept_3_3 95 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 94 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 241 (accept_3_3 92 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 241 (Polychromatic418967fa.accept_19_15_2_13_1_10598 91 97 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 241
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 90 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 241 (accept_3_3 89 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 241 (Polychromatic418967fa.accept_13_9_6_7_1_551 87 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 241 (accept_3_3 86 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 85 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 241
  (Polychromatic418967fa.accept_10_4_7_1_1_471 84 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 241 (accept_3_3 83 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 241 (Polychromatic418967fa.accept_13_4_6_7_1_2471 82 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 241 (accept_3_3 80 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 241
  (Polychromatic418967fa.accept_11_1_9_10_1_184 78 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 241 (accept_3_3 77 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 241 (Polychromatic418967fa.accept_10_6_7_1_1_1297 76 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 241 (Polychromatic418967fa.accept_17_7_12_3_1_4693 75 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 241 (accept_3_3 74 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 241 (Polychromatic418967fa.accept_19_16_2_13_1_13234 73 97
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 241 (accept_3_3 71 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 241 (Polychromatic418967fa.accept_15_10_7_1_1_3686 70 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 241 (Polychromatic418967fa.accept_13_4_6_7_1_2471 69 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 241 (accept_3_3 68 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 241
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 66 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 241 (accept_3_3 65 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 64 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 63 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 241 (accept_3_3 62 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 241 (Polychromatic418967fa.accept_13_9_6_7_1_551 61 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 241 (accept_3_3 59 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 241 (Polychromatic418967fa.accept_22_13_9_21_1_9862 57 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 241 (accept_3_3 56 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 241 (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 97
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 241
  (Polychromatic418967fa.accept_10_4_7_1_1_471 54 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 241 (accept_3_3 53 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 52 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 241 (accept_3_3 50 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 241 (Polychromatic418967fa.accept_17_15_12_3_1_8478 49 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 241
  (Polychromatic418967fa.accept_13_9_6_7_1_551 48 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 241 (accept_3_3 47 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 241 (accept_3_3 44 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 241 (Polychromatic418967fa.accept_13_4_6_7_1_2471 43 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 241
  (Polychromatic418967fa.accept_17_8_12_3_1_5927 42 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 241 (accept_3_3 41 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 241 (Polychromatic418967fa.accept_13_1_6_7_1_550 40 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 241 (accept_3_3 38 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 241
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 241 (accept_3_3 35 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 34 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 241 (Polychromatic418967fa.accept_23_10_5_11_1_14502 33 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 241 (accept_3_3 32 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 241 (Polychromatic418967fa.accept_20_11_17_1_1_13117 31 97
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 241 (accept_3_3 29 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 241 (Polychromatic418967fa.accept_21_7_13_10_1_8604 28 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 241 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 241 (accept_3_3 26 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 241
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 241 (accept_3_3 23 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 241 (Polychromatic418967fa.accept_13_9_6_7_1_551 22 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 241 (Polychromatic418967fa.accept_15_6_7_1_1_93 21 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 241 (accept_3_3 20 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 19 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 241 (accept_3_3 17 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 241 (Polychromatic418967fa.accept_17_15_12_3_1_8478 15 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 241 (accept_3_3 14 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 241 (Polychromatic418967fa.accept_22_13_9_21_1_9862 13 97
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 241
  (Polychromatic418967fa.accept_11_1_9_10_1_184 12 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 241 (accept_3_3 11 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 241 (Polychromatic418967fa.accept_14_10_13_3_1_2552 10 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 241 (accept_3_3 8 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 241 (Polychromatic418967fa.accept_17_7_12_3_1_4693 7 97 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 241
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 241 (accept_3_3 5 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 97 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 241 (Polychromatic418967fa.accept_21_3_13_10_1_11614 3 97 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 241 (accept_3_3 2 97 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 97 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 241
  (allA_succ_of_accept 95 96 241 (accept_3_3 95 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  96 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 94 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 96 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 96 241 (accept_3_3 92 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 241
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 90 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 96 241 (accept_3_3 89 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  96 241 (Polychromatic418967fa.accept_19_12_1_13_1_11823 88 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 96 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 87 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 241 (accept_3_3 86 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 241 (accept_3_3 83 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  96 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 241 (Polychromatic418967fa.accept_18_9_6_7_1_6719 81 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 241 (accept_3_3 80 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 78 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 96 241 (accept_3_3 77 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  96 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 96 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 241 (accept_3_3 74 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 241 (accept_3_3 71 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  96 241 (Polychromatic418967fa.accept_15_10_6_1_1_3707 70 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 241 (Polychromatic418967fa.accept_15_9_6_1_1_493 69 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 241 (accept_3_3 68 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 241 (accept_3_3 65 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 241 (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 241 (accept_3_3 62 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 241 (Polychromatic418967fa.accept_14_5_12_3_1_3397 61 96
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 241
  (Polychromatic418967fa.accept_17_9_11_3_1_2353 60 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 241 (accept_3_3 59 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 241 (accept_3_3 56 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 241
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 241 (accept_3_3 53 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 241 (accept_3_3 50 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 241 (accept_3_3 47 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 241 (accept_3_3 44 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 241
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 241 (accept_3_3 41 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 241 (accept_3_3 38 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 241 (accept_3_3 35 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 241 (Polychromatic418967fa.accept_22_12_8_21_1_14501 34 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 241 (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 241 (accept_3_3 32 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 96 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 241 (accept_3_3 29 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 241 (accept_3_3 26 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 241
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 241 (accept_3_3 23 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 241 (accept_3_3 20 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 241
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 241 (accept_3_3 17 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 241 (accept_3_3 14 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 241 (accept_3_3 11 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 241 (accept_3_3 8 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 96 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 241
  (Polychromatic418967fa.accept_20_6_16_1_1_7262 6 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 241 (accept_3_3 5 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  241 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 96 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 241 (accept_3_3 2 96 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 241
  (allA_of_3_1 95 95 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 241 (allA_succ_of_accept 93 94 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 94 241 (accept_3_3 92 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  94 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 94 241 (Polychromatic418967fa.accept_14_6_10_3_1_1038 90 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 241 (accept_3_3 89 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 88 94 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 94 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 94 241 (accept_3_3 86 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  94 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 85 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 94 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 241 (accept_3_3 83 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 241 (accept_3_3 80 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 78 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 241 (accept_3_3 77 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 76 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 241 (accept_3_3 74 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 241 (Polychromatic418967fa.accept_15_12_4_1_1_3746 72 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 241 (accept_3_3 71 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 241 (Polychromatic418967fa.accept_18_16_4_7_1_2927 70 94
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 241 (accept_3_3 68 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 241 (accept_3_3 65 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 241 (accept_3_3 62 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 241 (Polychromatic418967fa.accept_13_9_3_7_1_1065 61 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 241 (accept_3_3 59 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 241 (Polychromatic418967fa.accept_19_1_18_13_1_7796 58 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 241 (accept_3_3 56 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 241 (Polychromatic418967fa.accept_19_16_18_13_1_4855 54 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 241 (accept_3_3 53 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 94 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 241 (accept_3_3 50 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 241 (Polychromatic418967fa.accept_11_5_6_10_1_1432 49 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 241 (accept_3_3 47 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 241 (accept_3_3 44 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 241 (accept_3_3 41 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 241 (accept_3_3 38 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 241 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 241 (accept_3_3 35 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 241 (Polychromatic418967fa.accept_13_8_3_7_1_2455 34 94 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 241 (accept_3_3 32 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 241 (accept_3_3 29 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 241 (accept_3_3 26 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 241 (accept_3_3 23 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 241 (Polychromatic418967fa.accept_13_9_3_7_1_1065 22 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 241 (accept_3_3 20 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 241 (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 241 (accept_3_3 17 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 241 (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 241 (accept_3_3 14 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 241 (Polychromatic418967fa.accept_14_13_10_3_1_1037 13 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 241 (accept_3_3 11 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 94 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 241 (accept_3_3 8 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 94 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 241 (accept_3_3 5 94 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 94 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 241 (accept_3_3 2 94 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 94
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 241
  (allA_succ_of_accept 92 93 241 (accept_3_3 92 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 91 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 241 (accept_3_3 89 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 87 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 241 (accept_3_3 86 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 241 (accept_3_3 83 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 241
  (Polychromatic418967fa.accept_11_4_5_10_1_926 81 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 241 (accept_3_3 80 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 241 (Polychromatic418967fa.accept_15_4_3_1_1_487 79 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 241 (accept_3_3 77 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 241 (accept_3_3 74 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 241 (accept_3_3 71 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 241 (accept_3_3 68 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 241 (Polychromatic418967fa.accept_15_6_3_1_1_3678 66 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 241 (accept_3_3 65 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 241 (accept_3_3 62 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 241 (accept_3_3 59 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 241 (accept_3_3 56 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 241 (accept_3_3 53 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 241 (accept_3_3 50 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 241 (accept_3_3 47 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 241
  (Polychromatic418967fa.accept_18_9_3_7_1_9449 45 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 241 (accept_3_3 44 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 241 (accept_3_3 41 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 241
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 39 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 241 (accept_3_3 38 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 241 (accept_3_3 35 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 241 (accept_3_3 32 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 241 (Polychromatic418967fa.accept_16_14_13_1_1_5278 30 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 241 (accept_3_3 29 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 241 (accept_3_3 26 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 241 (Polychromatic418967fa.accept_16_9_13_1_1_3069 25 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 241 (accept_3_3 23 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 241
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 241 (accept_3_3 20 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 241 (accept_3_3 17 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 241 (accept_3_3 14 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 241 (accept_3_3 11 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 241
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 241 (accept_3_3 8 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  241 (Polychromatic418967fa.accept_19_7_17_13_1_9166 7 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 93 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 241 (accept_3_3 5 93 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 241 (accept_3_3 2 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93
  241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 93 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 92 241 (allA_of_3_1 92 92 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 241
  (allA_succ_of_accept 90 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 241 (accept_3_3 89 91 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 241 (Polychromatic418967fa.accept_14_4_7_3_1_1718 88 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 87
  91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 241 (accept_3_3 86 91
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 241
  (Polychromatic418967fa.accept_9_4_1_7_1_293 85 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 91 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 241 (accept_3_3 83 91 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 241 (Polychromatic418967fa.accept_14_11_7_3_1_3416
  81 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 241 (accept_3_3 80
  91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 241
  (Polychromatic418967fa.accept_16_15_11_1_1_7767 79 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 241 (accept_3_3 77 91 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 91 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 75
  91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 241 (accept_3_3 74 91
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 241
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 73 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 91 241 (Polychromatic418967fa.accept_20_12_11_1_1_3032 72 91 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 241 (accept_3_3 71 91 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 69
  91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 241 (accept_3_3 68 91
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 241
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 241 (accept_3_3 65 91 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 91 241 (Polychromatic418967fa.accept_19_7_15_13_1_9152 64 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 241
  (Polychromatic418967fa.accept_16_15_11_1_1_7767 63 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 241 (accept_3_3 62 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 241 (Polychromatic418967fa.accept_19_4_15_13_1_13215 61 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 241 (accept_3_3 59 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 241 (accept_3_3 56 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 241 (Polychromatic418967fa.accept_19_17_15_13_1_7794 55 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 241 (accept_3_3 53 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 241 (Polychromatic418967fa.accept_14_10_7_3_1_1022 52 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 241 (accept_3_3 50 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 241 (accept_3_3 47 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 241
  (Polychromatic418967fa.accept_19_7_15_13_1_9152 45 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 241 (accept_3_3 44 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 241 (Polychromatic418967fa.accept_17_9_6_3_1_2398 43 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 241 (accept_3_3 41 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 241 (accept_3_3 38 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 241 (Polychromatic418967fa.accept_20_17_11_1_1_8865 37 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 241 (Polychromatic418967fa.accept_19_17_15_13_1_7794 36 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 241 (accept_3_3 35 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 241 (accept_3_3 32 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 241 (accept_3_3 29 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 241 (Polychromatic418967fa.accept_16_12_11_1_1_4088 28 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 241
  (Polychromatic418967fa.accept_20_7_11_1_1_5840 27 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 241 (accept_3_3 26 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 241 (Polychromatic418967fa.accept_14_11_7_3_1_3416 25 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 241 (accept_3_3 23 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 241 (accept_3_3 20 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 241 (Polychromatic418967fa.accept_21_19_7_10_1_7006 19 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 241 (accept_3_3 17 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 241 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 241 (accept_3_3 14 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 241 (accept_3_3 11 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 241
  (Polychromatic418967fa.accept_17_9_6_3_1_2398 9 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 241 (accept_3_3 8 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 241 (accept_3_3 5 91 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 241 (accept_3_3 2 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  241 (Polychromatic418967fa.accept_17_1_6_3_1_4700 1 91 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 241
  (allA_succ_of_accept 89 90 241 (accept_3_3 89 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  90 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 241 (accept_3_3 86 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 241 (Polychromatic418967fa.accept_20_5_10_1_1_11750 85 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 241
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 84 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 241 (accept_3_3 83 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  90 241 (Polychromatic418967fa.accept_13_4_12_7_1_2439 82 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 90 241 (accept_3_3 80 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 241
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 78 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 90 241 (accept_3_3 77 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  90 241 (Polychromatic418967fa.accept_13_11_12_7_1_2443 76 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 90 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 241 (accept_3_3 74 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 241 (Polychromatic418967fa.accept_13_8_12_7_1_2442 73 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 90 241 (accept_3_3 71 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  90 241 (Polychromatic418967fa.accept_13_5_12_7_1_1080 70 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 90 241 (Polychromatic418967fa.accept_13_4_12_7_1_2439 69 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 241 (accept_3_3 68 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 241
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 66 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 90 241 (accept_3_3 65 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  90 241 (Polychromatic418967fa.accept_20_4_10_1_1_13131 64 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 90 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 241 (accept_3_3 62 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 241 (Polychromatic418967fa.accept_19_4_14_13_1_11820 61 90 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 90 241 (accept_3_3 59 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  90 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 90 241 (Polychromatic418967fa.accept_13_5_12_7_1_1080 57 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 241 (accept_3_3 56 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 241
  (Polychromatic418967fa.accept_19_16_14_13_1_2313 54 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 90 241 (accept_3_3 53 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 241 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 90 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 241 (accept_3_3 50 90 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 241
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 49 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 90 241 (Polychromatic418967fa.accept_22_4_2_21_1_11467 48 90 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 241 (accept_3_3 47 90 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 90 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 90 241 (Polychromatic418967fa.accept_11_1_2_10_1_1426
  45 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 241 (accept_3_3 44
  90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 90 241 (Polychromatic418967fa.accept_17_8_5_3_1_2397 42 90 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 241 (accept_3_3 41 90 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 90 241 (Polychromatic418967fa.accept_17_6_5_3_1_7134 40 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 241 (accept_3_3 38 90
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 90 241 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 90 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 241 (accept_3_3 35 90 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 90 241 (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 241
  (Polychromatic418967fa.accept_20_13_10_1_1_5903 33 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 90 241 (accept_3_3 32 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  90 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 90 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 241 (accept_3_3 29 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 241 (Polychromatic418967fa.accept_25_3_15_16_1_9190 28 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 90 241 (accept_3_3 26 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  90 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 90 241 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 241 (accept_3_3 23 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 241 (Polychromatic418967fa.accept_25_22_15_16_1_7286 22 90
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 241
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 90 241 (accept_3_3 20 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  90 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 90 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 241 (accept_3_3 17 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 90 241 (accept_3_3 14 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  90 241 (Polychromatic418967fa.accept_20_13_10_1_1_5903 13 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 90 241 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 241 (accept_3_3 11 90 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 241 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 90
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 241 (accept_3_3 8 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90
  241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 90 241 (Polychromatic418967fa.accept_13_6_12_7_1_5131 6 90 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 241 (accept_3_3 5 90 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 90 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 90 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 241 (accept_3_3 2 90 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 241 (Polychromatic418967fa.accept_11_1_2_10_1_1426
  1 90 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 241
  (allA_of_3_1 89 89 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 241 (allA_succ_of_accept 87 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 88 241 (accept_3_3 86 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  88 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 88 241 (Polychromatic418967fa.accept_16_4_8_1_1_5257 84 88 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 241 (accept_3_3 83 88 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 82 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 88 241 (accept_3_3 80 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  88 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 79 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 88 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 88 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 241 (accept_3_3 77 88 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 241 (accept_3_3 74 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 73 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 241 (Polychromatic418967fa.accept_15_12_13_1_1_3695 72 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 241 (accept_3_3 71 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 88
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 241 (accept_3_3 68 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 241 (Polychromatic418967fa.accept_20_7_8_1_1_5856 67 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 88 241 (Polychromatic418967fa.accept_29_8_1_9_1_14500 66 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 241 (accept_3_3 65 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 88 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 88 241 (accept_3_3 62 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  88 241 (Polychromatic418967fa.accept_21_19_4_10_1_3914 61 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 88 241 (Polychromatic418967fa.accept_13_8_10_7_1_1702 60 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 241 (accept_3_3 59 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 88
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 241 (accept_3_3 56 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 241 (Polychromatic418967fa.accept_19_16_12_13_1_4843 54 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 241 (accept_3_3 53 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 241 (Polychromatic418967fa.accept_16_4_8_1_1_5257 52 88 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 241 (accept_3_3 50 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 88 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 241 (accept_3_3 47 88 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 241 (accept_3_3 44 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 241 (Polychromatic418967fa.accept_13_3_10_7_1_1061 42 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 241 (accept_3_3 41 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 88
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 241 (accept_3_3 38 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 241 (Polychromatic418967fa.accept_18_1_16_7_1_2897 37 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 88 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 241 (accept_3_3 35 88 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 241 (accept_3_3 32 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 241 (Polychromatic418967fa.accept_16_15_8_1_1_9959 31 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 241 (Polychromatic418967fa.accept_13_4_10_7_1_1701 30 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 241 (accept_3_3 29 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 241 (Polychromatic418967fa.accept_16_12_8_1_1_5270 28 88
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 241 (accept_3_3 26 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 241 (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 241 (Polychromatic418967fa.accept_19_5_12_13_1_9115 24 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 241 (accept_3_3 23 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 88 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 241 (accept_3_3 20 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 241 (Polychromatic418967fa.accept_15_3_13_1_1_479 18 88 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 241 (accept_3_3 17 88 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 241 (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 241 (accept_3_3 14 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 241 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 241 (accept_3_3 11 88 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 88
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 241 (accept_3_3 8 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  241 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 88 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 88 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 88 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 241 (accept_3_3 5 88 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 88 241 (Polychromatic418967fa.accept_13_4_10_7_1_1701 4 88 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 241 (accept_3_3 2 88 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 88
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 241
  (allA_succ_of_accept 86 87 241 (accept_3_3 86 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  87 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 85 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 84 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 241 (accept_3_3 83 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 81 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 241 (accept_3_3 80 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 241 (Polychromatic418967fa.accept_15_4_12_1_1_1081 79 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 241 (accept_3_3 77 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 75 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 241 (accept_3_3 74 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 241 (Polychromatic418967fa.accept_16_8_7_1_1_8875 72 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 241 (accept_3_3 71 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 69 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 241 (accept_3_3 68 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 241 (accept_3_3 65 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 241
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 241 (accept_3_3 62 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 241 (Polychromatic418967fa.accept_28_5_3_17_1_14499 61 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 241 (Polychromatic418967fa.accept_13_8_9_7_1_530 60 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 241 (accept_3_3 59 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 241 (accept_3_3 56 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 241 (accept_3_3 53 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 241
  (Polychromatic418967fa.accept_20_11_7_1_1_8874 51 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 241 (accept_3_3 50 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 241 (accept_3_3 47 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 241 (accept_3_3 44 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 241 (Polychromatic418967fa.accept_13_4_9_7_1_2402 43 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 241 (accept_3_3 41 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 241 (accept_3_3 38 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 241 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 241 (accept_3_3 35 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 241 (accept_3_3 32 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 241 (accept_3_3 29 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 241
  (Polychromatic418967fa.accept_23_4_18_11_1_14498 27 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 241 (accept_3_3 26 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 241 (Polychromatic418967fa.accept_19_6_11_13_1_4842 25 87 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 241 (accept_3_3 23 87 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 241 (accept_3_3 20 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 241 (accept_3_3 17 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 241
  (Polychromatic418967fa.accept_13_2_9_7_1_164 15 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 241 (accept_3_3 14 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 241 (accept_3_3 11 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 241 (accept_3_3 8 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  241 (Polychromatic418967fa.accept_19_7_11_13_1_11853 7 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 87 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 241 (accept_3_3 5 87 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 241 (accept_3_3 2 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87
  241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 87 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 87 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86
  241 (allA_of_3_1 86 86 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 241 (allA_succ_of_accept 84 85 241
  (Polychromatic418967fa.accept_8_4_5_1_1_299 84 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 241 (accept_3_3 83 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 241 (accept_3_3 80 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 241 (accept_3_3 77 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 76 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 241 (accept_3_3 74 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 241 (accept_3_3 71 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 241 (Polychromatic418967fa.accept_16_6_5_1_1_7761 70 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 241 (accept_3_3 68 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 241 (accept_3_3 65 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 241 (Polychromatic418967fa.accept_16_15_5_1_1_7724 63 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 241 (accept_3_3 62 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 85 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 241 (accept_3_3 59 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 241 (accept_3_3 56 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 241 (accept_3_3 53 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 241 (accept_3_3 50 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 241 (accept_3_3 47 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 241 (Polychromatic418967fa.accept_16_13_5_1_1_3017 45 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 241 (accept_3_3 44 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 85
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 241 (accept_3_3 41 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 241 (accept_3_3 38 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 241
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 241 (accept_3_3 35 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 34 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 241 (accept_3_3 32 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 31 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 241 (accept_3_3 29 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 241 (Polychromatic418967fa.accept_23_4_16_11_1_14497 27 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 241 (accept_3_3 26 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 85 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 241 (accept_3_3 23 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 241 (accept_3_3 20 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 241 (accept_3_3 17 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 241 (accept_3_3 14 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 241 (accept_3_3 11 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 241 (accept_3_3 8 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 85 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 241 (accept_3_3 5 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 85 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 85 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 241 (accept_3_3 2 85 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 241
  (allA_succ_of_accept 83 84 241 (accept_3_3 83 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 241 (Polychromatic418967fa.accept_15_6_9_1_1_1823 81 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 241 (accept_3_3 80 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 241 (Polychromatic418967fa.accept_13_1_6_7_1_550 79 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 84 241 (accept_3_3 77 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  84 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 84 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 75 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 241 (accept_3_3 74 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 241
  (Polychromatic418967fa.accept_16_8_4_1_1_2102 72 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 241 (accept_3_3 71 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 241 (Polychromatic418967fa.accept_15_10_9_1_1_3688 70 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 241 (accept_3_3 68 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 241
  (Polychromatic418967fa.accept_13_1_6_7_1_550 66 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 84 241 (accept_3_3 65 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  84 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 241 (Polychromatic418967fa.accept_19_6_8_13_1_14496 63 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 241 (accept_3_3 62 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 84 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 241 (accept_3_3 59 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 241 (accept_3_3 56 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 241
  (Polychromatic418967fa.accept_22_10_18_21_1_8227 54 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 84 241 (accept_3_3 53 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 241 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 84 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 84 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 84 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 241 (accept_3_3 50 84 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49
  84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 241
  (Polychromatic418967fa.accept_13_9_6_7_1_551 48 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 241 (accept_3_3 47 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 241 (accept_3_3 44 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 241 (Polychromatic418967fa.accept_13_4_6_7_1_2471 43 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 241 (accept_3_3 41 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 241 (Polychromatic418967fa.accept_18_3_12_7_1_6728 39 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 241 (accept_3_3 38 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 84 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 241
  (Polychromatic418967fa.accept_11_3_7_10_1_180 36 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 241 (accept_3_3 35 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 241 (Polychromatic418967fa.accept_27_7_3_25_1_14495 34 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 241 (accept_3_3 32 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 241
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 30 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 241 (accept_3_3 29 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 241 (accept_3_3 26 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 241 (accept_3_3 23 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 241 (accept_3_3 20 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 241
  (Polychromatic418967fa.accept_19_18_8_13_1_6303 18 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 241 (accept_3_3 17 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 241 (Polychromatic418967fa.accept_24_16_12_1_1_14494 16 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 241 (accept_3_3 14 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 241
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 241 (accept_3_3 11 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 241 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 241 (accept_3_3 8 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 84 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 241 (accept_3_3 5 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  241 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 84 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 84 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 241 (accept_3_3 2 84 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 241 (allA_of_3_1
  83 83 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 241 (allA_succ_of_accept 81 82 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 241 (accept_3_3 80 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 241 (accept_3_3 77 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 241 (accept_3_3 74 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 73 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 241 (accept_3_3 71 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 70 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 241 (accept_3_3 68 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 241 (accept_3_3 65 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 241 (accept_3_3 62 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 241 (Polychromatic418967fa.accept_11_6_5_10_1_2724 61 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 241 (accept_3_3 59 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 241 (accept_3_3 56 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 241 (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 241 (accept_3_3 53 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 241 (accept_3_3 50 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 241 (accept_3_3 47 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 241 (accept_3_3 44 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 241 (accept_3_3 41 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 241 (accept_3_3 38 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 241 (accept_3_3 35 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 241 (Polychromatic418967fa.accept_19_15_6_13_1_10577 34 82 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 241 (accept_3_3 32 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 241 (accept_3_3 29 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 241 (Polychromatic418967fa.accept_11_6_5_10_1_2724 28 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 241 (accept_3_3 26 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 241 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 241 (accept_3_3 23 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 241 (accept_3_3 20 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 241 (Polychromatic418967fa.accept_23_18_13_11_1_14493 18 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 241 (accept_3_3 17 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 82 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 241 (accept_3_3 14 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 241 (accept_3_3 11 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 241 (Polychromatic418967fa.accept_13_10_4_7_1_2465 10 82 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 241 (accept_3_3 8 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 82 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 241 (accept_3_3 5 82 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 82 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 241 (accept_3_3 2 82 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  82 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 241
  (allA_succ_of_accept 80 81 241 (accept_3_3 80 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 241 (Polychromatic418967fa.accept_13_1_3_7_1_1710 79 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 241 (accept_3_3 77 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 241 (accept_3_3 74 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 241 (Polychromatic418967fa.accept_13_8_3_7_1_2455 73 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 241 (Polychromatic418967fa.accept_17_4_13_3_1_7166 72 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 241 (accept_3_3 71 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 81 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 241 (accept_3_3 68 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 241 (Polychromatic418967fa.accept_15_7_6_1_1_1091 67 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 241 (Polychromatic418967fa.accept_13_1_3_7_1_1710 66 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 241 (accept_3_3 65 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 241 (accept_3_3 62 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 241 (Polychromatic418967fa.accept_13_9_3_7_1_1065 61 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 241 (Polychromatic418967fa.accept_11_5_4_10_1_524 60 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 241 (accept_3_3 59 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 241 (accept_3_3 56 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 241 (Polychromatic418967fa.accept_15_9_6_1_1_493 54 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 241 (accept_3_3 53 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 241 (accept_3_3 50 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 241 (Polychromatic418967fa.accept_11_5_4_10_1_524 49 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 241 (accept_3_3 47 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 241
  (Polychromatic418967fa.accept_19_7_5_13_1_3493 45 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 241 (accept_3_3 44 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 241 (Polychromatic418967fa.accept_17_8_13_3_1_3432 42 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 241 (accept_3_3 41 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 241 (accept_3_3 38 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 241 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 241 (accept_3_3 35 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 241
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 241 (accept_3_3 32 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 241 (Polychromatic418967fa.accept_19_12_5_13_1_14492 31 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 241 (Polychromatic418967fa.accept_13_4_3_7_1_2515 30 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 241 (accept_3_3 29 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 241 (accept_3_3 26 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 241 (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 241 (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 241 (accept_3_3 23 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 81 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 241
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 241 (accept_3_3 20 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 241 (Polychromatic418967fa.accept_23_19_12_11_1_9742 19 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 241 (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 241 (accept_3_3 17 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 241 (accept_3_3 14 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 241 (Polychromatic418967fa.accept_19_12_5_13_1_14492 12 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 241 (accept_3_3 11 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 81 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 241
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 241 (accept_3_3 8 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 241 (accept_3_3 5 81 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 241 (accept_3_3 2 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 81 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 241
  (allA_of_3_1 80 80 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 241 (allA_succ_of_accept 78 79 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 241 (accept_3_3 77 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 241 (accept_3_3 74 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 241 (Polychromatic418967fa.accept_13_8_1_7_1_2505 73 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 241
  (Polychromatic418967fa.accept_10_2_9_1_1_185 72 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 241 (accept_3_3 71 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 241 (accept_3_3 68 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 241 (Polychromatic418967fa.accept_11_1_2_10_1_1426 67 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 241 (accept_3_3 65 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 241 (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 241 (accept_3_3 62 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 79 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 241
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 60 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 241 (accept_3_3 59 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 241 (accept_3_3 56 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 241 (accept_3_3 53 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 241 (Polychromatic418967fa.accept_10_2_9_1_1_185 52 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 241 (Polychromatic418967fa.accept_21_9_16_10_1_5371 51 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 241 (accept_3_3 50 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 241 (Polychromatic418967fa.accept_19_11_3_13_1_9178 49 79
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 241 (accept_3_3 47 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 241 (accept_3_3 44 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 241 (accept_3_3 41 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 241 (Polychromatic418967fa.accept_22_17_13_21_1_11455 39 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 241 (accept_3_3 38 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 241 (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 79
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 241 (accept_3_3 35 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 241 (accept_3_3 32 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 241 (Polychromatic418967fa.accept_17_14_11_3_1_4653 31 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 241 (accept_3_3 29 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 241 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 241 (accept_3_3 26 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 241
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 241 (accept_3_3 23 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 241 (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 241 (accept_3_3 20 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 241 (accept_3_3 17 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 241 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 241 (accept_3_3 14 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 241 (accept_3_3 11 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 241 (Polychromatic418967fa.accept_17_9_11_3_1_2353 9 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 241 (accept_3_3 8 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 241 (Polychromatic418967fa.accept_19_7_3_13_1_3492 7 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 241 (accept_3_3 5 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  241 (Polychromatic418967fa.accept_19_4_3_13_1_6317 4 79 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 79 241 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 241 (accept_3_3 2 79 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 79 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 241
  (allA_succ_of_accept 77 78 241 (accept_3_3 77 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 241 (accept_3_3 74 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 241 (accept_3_3 71 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 241 (Polychromatic418967fa.accept_21_7_15_10_1_1368 70 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 241 (accept_3_3 68 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 241 (accept_3_3 65 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 241 (accept_3_3 62 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 241 (accept_3_3 59 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 241 (accept_3_3 56 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 241 (accept_3_3 53 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 241 (Polychromatic418967fa.accept_16_4_14_1_1_1241 52 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 241 (accept_3_3 50 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 241 (accept_3_3 47 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 241 (Polychromatic418967fa.accept_16_13_14_1_1_2094 45 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 241 (accept_3_3 44 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 241
  (Polychromatic418967fa.accept_11_9_1_10_1_920 42 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 241 (accept_3_3 41 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 241 (accept_3_3 38 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 241
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 241 (accept_3_3 35 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 241 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 241 (accept_3_3 32 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 241 (accept_3_3 29 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 241 (accept_3_3 26 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 241
  (Polychromatic418967fa.accept_11_2_1_10_1_196 24 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 241 (accept_3_3 23 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 241 (accept_3_3 20 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 241 (accept_3_3 17 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 241 (accept_3_3 14 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 241 (accept_3_3 11 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 241 (accept_3_3 8 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 241
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 241 (accept_3_3 5 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 78 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 241 (accept_3_3 2 78 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 241 (allA_of_3_1 77 77
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 241 (allA_succ_of_accept 75 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 241 (accept_3_3 74 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 241 (accept_3_3 71 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 241 (accept_3_3 68 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 241 (accept_3_3 65 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 241 (accept_3_3 62 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 241 (accept_3_3 59 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 241 (accept_3_3 56 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 241 (Polychromatic418967fa.accept_25_4_1_16_1_14491 54 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 241 (accept_3_3 53 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 76 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 241 (accept_3_3 50 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 241 (Polychromatic418967fa.accept_18_13_4_7_1_4086 49 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 241 (accept_3_3 47 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 241 (accept_3_3 44 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 241 (Polychromatic418967fa.accept_13_4_11_7_1_558 43 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 241 (accept_3_3 41 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 241 (Polychromatic418967fa.accept_13_1_11_7_1_1704 40 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 241 (accept_3_3 38 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 241 (Polychromatic418967fa.accept_16_4_12_1_1_1204 36 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 241 (accept_3_3 35 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 76
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 241 (accept_3_3 32 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 241 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 241 (accept_3_3 29 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 241 (accept_3_3 26 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 241 (accept_3_3 23 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 241 (accept_3_3 20 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 241 (accept_3_3 17 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 241 (accept_3_3 14 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 241 (accept_3_3 11 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 76 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 241 (accept_3_3 8 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  241 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 76 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 76 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 241 (accept_3_3 5 76 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 76 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 241 (accept_3_3 2 76 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 241 (allA_succ_of_accept
  74 75 241 (accept_3_3 74 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 241
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 75 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 241 (accept_3_3 71 75 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 69
  75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 241 (accept_3_3 68 75
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 241
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 75 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 241 (accept_3_3 65 75 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 75 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 241 (Polychromatic418967fa.accept_11_8_9_10_1_503
  63 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 241 (accept_3_3 62
  75 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 241
  (Polychromatic418967fa.accept_17_10_7_3_1_727 61 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 75 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 75 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 241 (accept_3_3 59 75 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 57
  75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 241 (accept_3_3 56 75
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 241 (Polychromatic418967fa.accept_9_1_3_7_1_6
  55 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 241 (accept_3_3 53 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 241 (accept_3_3 50 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 75 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 241
  (Polychromatic418967fa.accept_18_12_3_7_1_5373 48 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 241 (accept_3_3 47 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 241 (accept_3_3 44 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 75 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 241 (accept_3_3 41 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 241 (accept_3_3 38 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 75 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 241 (accept_3_3 35 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 241 (accept_3_3 32 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 75 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 241 (accept_3_3 29 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 241 (Polychromatic418967fa.accept_17_10_7_3_1_727 27 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 241 (accept_3_3 26 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 241 (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 75 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 241 (accept_3_3 23 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 241 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 241 (accept_3_3 20 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 75 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 241 (accept_3_3 17 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 241 (accept_3_3 14 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 75 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 241
  (Polychromatic418967fa.accept_11_1_9_10_1_184 12 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 241 (accept_3_3 11 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 241 (accept_3_3 8 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 241 (Polychromatic418967fa.accept_20_7_15_1_1_13089 7 75 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 241 (accept_3_3 5 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 241 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 75 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 241 (accept_3_3 2 75 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 75 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 241 (allA_of_3_1 74 74
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 241 (allA_succ_of_accept 72 73 241
  (Polychromatic418967fa.accept_10_2_3_1_1_481 72 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 241 (accept_3_3 71 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 70 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 241 (accept_3_3 68 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 241 (accept_3_3 65 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 241 (Polychromatic418967fa.accept_13_12_8_7_1_2526 64 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 241 (Polychromatic418967fa.accept_15_3_13_1_1_479 63 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 241 (accept_3_3 62 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 241 (Polychromatic418967fa.accept_13_9_8_7_1_1073 61 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 241 (accept_3_3 59 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 241 (accept_3_3 56 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 241 (Polychromatic418967fa.accept_13_3_8_7_1_4135 55 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 241
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 54 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 241 (accept_3_3 53 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 52 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 241 (accept_3_3 50 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 241 (accept_3_3 47 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 241 (Polychromatic418967fa.accept_25_21_23_16_1_14490 46 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 241 (Polychromatic418967fa.accept_16_13_9_1_1_3022 45 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 241 (accept_3_3 44 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 241 (Polychromatic418967fa.accept_20_3_13_1_1_8886 43 73
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 241 (accept_3_3 41 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 241 (accept_3_3 38 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 241 (Polychromatic418967fa.accept_16_5_9_1_1_2070 37 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 241
  (Polychromatic418967fa.accept_11_3_7_10_1_180 36 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 241 (accept_3_3 35 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 241 (Polychromatic418967fa.accept_16_2_9_1_1_6404 34 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 241 (accept_3_3 32 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 241 (accept_3_3 29 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 241 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 241 (accept_3_3 26 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 241 (accept_3_3 23 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 241 (accept_3_3 20 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 241 (Polychromatic418967fa.accept_17_2_5_3_1_1416 19 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 241
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 241 (accept_3_3 17 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 241 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 241 (accept_3_3 14 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 241 (accept_3_3 11 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 241 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 241 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 241 (accept_3_3 8 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 241 (Polychromatic418967fa.accept_23_7_4_11_1_14489 7 73 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 241 (accept_3_3 5 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 73 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 73 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 241 (accept_3_3 2 73 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 241 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 73 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 241 (allA_succ_of_accept 71
  72 241 (accept_3_3 71 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 241
  (Polychromatic418967fa.accept_21_7_9_10_1_2573 70 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 72 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 241 (accept_3_3 68 72 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 241 (Polychromatic418967fa.accept_17_16_4_3_1_3429 67 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 66 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 72 241 (accept_3_3 65 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  72 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 72 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 241 (accept_3_3 62 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 241
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 60 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 241 (accept_3_3 59 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  72 241 (Polychromatic418967fa.accept_15_13_12_1_1_1841 58 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 241 (accept_3_3 56 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 72 241 (accept_3_3 53 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  72 241 (Polychromatic418967fa.accept_16_4_8_1_1_5257 52 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 241 (Polychromatic418967fa.accept_20_11_12_1_1_13132 51 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 241 (accept_3_3 50 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 72 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 241 (accept_3_3 47 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 241 (Polychromatic418967fa.accept_19_7_15_13_1_9152 45 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 241 (accept_3_3 44 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 72 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 241
  (Polychromatic418967fa.accept_19_4_15_13_1_13215 42 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 72 241 (accept_3_3 41 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 72 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 72 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 72 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 241 (accept_3_3 38 72 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 241
  (Polychromatic418967fa.accept_21_16_9_10_1_14488 37 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 72 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 241 (accept_3_3 35 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 72 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 72 241 (accept_3_3 32 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  72 241 (Polychromatic418967fa.accept_16_15_8_1_1_9959 31 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 72 241 (Polychromatic418967fa.accept_17_13_4_3_1_1446 30 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 241 (accept_3_3 29 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 241 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 72
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 72 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 72 241 (accept_3_3 26 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  72 241 (Polychromatic418967fa.accept_16_9_8_1_1_1228 25 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 72 241 (Polychromatic418967fa.accept_17_7_4_3_1_3456 24 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 241 (accept_3_3 23 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 72 241
  (Polychromatic418967fa.accept_19_2_15_13_1_4897 21 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 72 241 (accept_3_3 20 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  72 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 72 241 (Polychromatic418967fa.accept_21_18_9_10_1_2571 18 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 241 (accept_3_3 17 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 72 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 72 241 (accept_3_3 14 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  72 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 72 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 241 (accept_3_3 11 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 241 (Polychromatic418967fa.accept_22_10_6_21_1_8302 10 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 241
  (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 72 241 (accept_3_3 8 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72
  241 (Polychromatic418967fa.accept_16_7_8_1_1_3061 7 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 72 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 241 (accept_3_3 5 72 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 241 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 72 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72 241
  (Polychromatic418967fa.accept_10_3_2_1_1_839 3 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 241 (accept_3_3 2 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72
  241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 241
  (allA_of_3_1 71 71 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 241 (allA_succ_of_accept 69 70 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 241 (accept_3_3 68 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 241 (Polychromatic418967fa.accept_15_6_10_1_1_3675 66 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 241 (accept_3_3 65 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 70 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 241 (accept_3_3 62 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 241 (Polychromatic418967fa.accept_21_19_7_10_1_7006 61 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 241 (Polychromatic418967fa.accept_11_5_4_10_1_524 60 70 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 241 (accept_3_3 59 70 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 58 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 241 (accept_3_3 56 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 241 (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 70 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 241 (accept_3_3 53 70 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 241 (accept_3_3 50 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 241 (Polychromatic418967fa.accept_11_5_4_10_1_524 49 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 241 (Polychromatic418967fa.accept_17_14_2_3_1_7172 48 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 241 (accept_3_3 47 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 241 (Polychromatic418967fa.accept_22_2_4_21_1_8235 46 70
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 241 (accept_3_3 44 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 241 (Polychromatic418967fa.accept_22_20_4_21_1_8237 42 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 241 (accept_3_3 41 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 70 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 241 (accept_3_3 38 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 241 (Polychromatic418967fa.accept_13_11_5_7_1_2420 37 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 241 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 241 (accept_3_3 35 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 241 (Polychromatic418967fa.accept_16_2_6_1_1_2069 34 70 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 241 (accept_3_3 32 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 241 (Polychromatic418967fa.accept_21_9_7_10_1_3907 30 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 241 (accept_3_3 29 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 70 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 241 (accept_3_3 26 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 241 (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 241 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 241 (accept_3_3 23 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 70
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 241 (accept_3_3 20 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 241 (Polychromatic418967fa.accept_16_2_6_1_1_2069 18 70 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 241 (accept_3_3 17 70 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 241 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 241 (accept_3_3 14 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 241 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 241 (accept_3_3 11 70 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 241 (Polychromatic418967fa.accept_23_10_1_11_1_14487 10 70
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 241 (accept_3_3 8 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 241 (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 70 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 241 (accept_3_3 5 70 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 70 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 70 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 241 (accept_3_3 2 70 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 241 (Polychromatic418967fa.accept_17_1_2_3_1_4668 1
  70 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 241 (allA_succ_of_accept 68 69
  241 (accept_3_3 68 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 241 (accept_3_3 65 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 241 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 241 (accept_3_3 62
  69 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 241
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 61 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 69 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 241 (accept_3_3 59 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 69 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 57
  69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 241 (accept_3_3 56 69
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 241
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 69 241 (Polychromatic418967fa.accept_16_6_5_1_1_7761 54 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 241 (accept_3_3 53 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 69 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 51
  69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 241 (accept_3_3 50 69
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 241
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 69 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 241 (accept_3_3 47 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 69 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 241 (Polychromatic418967fa.accept_10_5_9_1_1_187
  45 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 241 (accept_3_3 44
  69 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 241
  (Polychromatic418967fa.accept_17_9_1_3_1_4626 43 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 69 241 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 241 (accept_3_3 41 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 69 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 39
  69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 241 (accept_3_3 38 69
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 69 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 241 (accept_3_3 35 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 69 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 241
  (Polychromatic418967fa.accept_19_14_12_13_1_3485 33 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 69 241 (accept_3_3 32 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 69 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 69 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 241 (accept_3_3 29 69 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 241 (accept_3_3 26 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 241 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 69 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 241 (accept_3_3 23 69 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 69 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 241 (accept_3_3 20 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 241 (accept_3_3 17 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 241
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 241 (accept_3_3 14 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 241 (accept_3_3 11 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 241 (accept_3_3 8 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 69 241 (Polychromatic418967fa.accept_13_6_4_7_1_2464 6 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 241 (accept_3_3 5 69 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 241 (accept_3_3 2 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69
  241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 69 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 241 (allA_of_3_1
  68 68 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 241 (allA_succ_of_accept 66 67 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 241 (accept_3_3 65 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 241 (accept_3_3 62 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 241 (Polychromatic418967fa.accept_13_9_2_7_1_1083 61 67 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 241 (accept_3_3 59 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 241 (accept_3_3 56 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 241 (accept_3_3 53 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 241 (Polychromatic418967fa.accept_16_4_3_1_1_8843 52 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 241 (accept_3_3 50 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 49 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 241 (accept_3_3 47 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 241 (Polychromatic418967fa.accept_16_13_3_1_1_2100 45 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 241 (accept_3_3 44 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 67 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 241 (accept_3_3 41 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 241 (Polychromatic418967fa.accept_15_10_7_1_1_3686 40 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 241 (accept_3_3 38 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 241 (accept_3_3 35 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 241 (accept_3_3 32 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 241 (accept_3_3 29 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 241 (accept_3_3 26 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 241 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 241 (accept_3_3 23 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 241 (accept_3_3 20 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 241 (accept_3_3 17 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 241 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 241 (accept_3_3 14 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 241 (accept_3_3 11 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 241 (accept_3_3 8 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 67 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 241 (accept_3_3 5 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  241 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 67 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 67 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 241 (accept_3_3 2 67 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 67 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 241 (allA_succ_of_accept 65 66
  241 (accept_3_3 65 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 241
  (Polychromatic418967fa.accept_9_1_3_7_1_6 64 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 241 (accept_3_3 62 66 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 241 (Polychromatic418967fa.accept_19_4_9_13_1_7792 61 66 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 66 241 (accept_3_3 59 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  66 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 66 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 57 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 241 (accept_3_3 56 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 241
  (Polychromatic418967fa.accept_15_9_6_1_1_493 54 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 66 241 (accept_3_3 53 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  66 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 66 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 241 (accept_3_3 50 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 66 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 241
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 66 241 (accept_3_3 47 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  66 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 66 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 241 (accept_3_3 44 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 66 241 (accept_3_3 41 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  66 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 66 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 241 (accept_3_3 38 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 66 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 241
  (Polychromatic418967fa.accept_19_17_9_13_1_6325 36 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 241 (accept_3_3 35 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  66 241 (Polychromatic418967fa.accept_13_8_1_7_1_2505 34 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 241 (accept_3_3 32 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 241
  (Polychromatic418967fa.accept_21_9_3_10_1_8573 30 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 66 241 (accept_3_3 29 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  66 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 66 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 241 (accept_3_3 26 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 66 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 241 (accept_3_3 23 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  66 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 66 241 (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 241 (accept_3_3 20 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 241
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 241 (accept_3_3 17 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  66 241 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 241 (accept_3_3 14 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 66 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 241
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 66 241 (accept_3_3 11 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  66 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 66 241 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 241 (accept_3_3 8 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 241 (accept_3_3 5 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  241 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 66 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 66 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 241 (accept_3_3 2 66 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 66 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 66 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 241 (allA_of_3_1 65 65 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 241 (allA_succ_of_accept 63 64 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 241 (accept_3_3 62 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 241 (accept_3_3 59 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 64 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 241 (accept_3_3 56 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 241 (accept_3_3 53 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 52 64 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 241 (accept_3_3 50 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 241 (accept_3_3 47 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 64 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 241 (accept_3_3 44 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 241 (Polychromatic418967fa.accept_13_4_12_7_1_2439 43 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 241 (accept_3_3 41 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 64 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 241 (accept_3_3 38 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 241 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 64 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 241 (accept_3_3 35 64 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 34 64 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 241 (accept_3_3 32 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 241 (accept_3_3 29 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 241 (Polychromatic418967fa.accept_19_9_7_13_1_7780 28 64 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 241 (accept_3_3 26 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 241 (accept_3_3 23 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 64 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 241 (accept_3_3 20 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 241 (accept_3_3 17 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 64 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 241 (accept_3_3 14 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 241 (accept_3_3 11 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 64 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 241 (accept_3_3 8 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 64 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 241 (accept_3_3 5 64 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 64 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 241 (accept_3_3 2 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  241 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 64 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 64 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 241
  (allA_succ_of_accept 62 63 241 (accept_3_3 62 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 241 (Polychromatic418967fa.accept_13_9_11_7_1_1077 61 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 241 (Polychromatic418967fa.accept_14_4_7_3_1_1718 60 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 241 (accept_3_3 59 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 241 (accept_3_3 56 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 241 (Polychromatic418967fa.accept_13_3_11_7_1_2488 55 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 241 (accept_3_3 53 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 241
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 241 (accept_3_3 50 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 241 (Polychromatic418967fa.accept_15_4_3_1_1_487 49 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 241 (accept_3_3 47 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 241 (accept_3_3 44 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 241 (Polychromatic418967fa.accept_13_4_11_7_1_558 43 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 241 (accept_3_3 41 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 241
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 241 (accept_3_3 38 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 241 (Polychromatic418967fa.accept_16_5_15_1_1_2113 37 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 241 (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 241 (accept_3_3 35 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 241 (accept_3_3 32 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 31 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 241 (accept_3_3 29 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 241
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 241 (accept_3_3 26 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 241 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 241 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 63 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 241 (accept_3_3 23 63 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 241 (accept_3_3 20 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 241 (Polychromatic418967fa.accept_15_4_3_1_1_487 19 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 241 (accept_3_3 17 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 241
  (Polychromatic418967fa.accept_17_15_12_3_1_8478 15 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 241 (accept_3_3 14 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 241 (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 241 (accept_3_3 11 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 241
  (Polychromatic418967fa.accept_11_9_8_10_1_934 9 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 241 (accept_3_3 8 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  241 (Polychromatic418967fa.accept_17_7_12_3_1_4693 7 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 241 (accept_3_3 5 63 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 241
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 241 (accept_3_3 2 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  241 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 63 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 241
  (allA_of_3_1 62 62 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 241 (allA_succ_of_accept 60 61 241
  (Polychromatic418967fa.accept_8_4_5_1_1_299 60 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 241 (accept_3_3 59 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 61 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 241 (accept_3_3 56 61 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 241 (Polychromatic418967fa.accept_13_3_9_7_1_1730 55 61 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 241
  (Polychromatic418967fa.accept_13_2_9_7_1_164 54 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 241 (accept_3_3 53 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 61 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 241 (accept_3_3 50 61 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 241 (Polychromatic418967fa.accept_11_5_6_10_1_1432 49 61 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 241
  (Polychromatic418967fa.accept_19_10_4_13_1_14484 48 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 61 241 (accept_3_3 47 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 61 241 (Polychromatic418967fa.accept_16_14_13_1_1_5278 46 61 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 61 241 (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 61 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 241 (accept_3_3 44 61 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 43
  61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 241
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 42 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 241 (accept_3_3 41 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 241 (Polychromatic418967fa.accept_14_12_5_3_1_1011 40 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 241 (Polychromatic418967fa.accept_25_14_11_16_1_14486 39 61 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 241 (accept_3_3 38 61 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 61 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 241 (accept_3_3 35 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 241 (Polychromatic418967fa.accept_13_8_9_7_1_530 34 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 241 (Polychromatic418967fa.accept_19_14_4_13_1_7779 33 61 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 241 (accept_3_3 32 61 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 241 (Polychromatic418967fa.accept_24_7_13_1_1_9522 31 61
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 241 (accept_3_3 29 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 241 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 61 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 241 (accept_3_3 26 61 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 241 (Polychromatic418967fa.accept_16_9_13_1_1_3069 25 61
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 241
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 241 (accept_3_3 23 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 241 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 61 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 241 (accept_3_3 20 61 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 241 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 61 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 241
  (Polychromatic418967fa.accept_22_18_17_21_1_14485 18 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 61 241 (accept_3_3 17 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 61 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 61 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 61 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 241 (accept_3_3 14 61 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 241
  (Polychromatic418967fa.accept_17_13_10_3_1_7136 13 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 61 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 61 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 241 (accept_3_3 11 61 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 61 241 (Polychromatic418967fa.accept_19_10_4_13_1_14484 10 61 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 61 241 (accept_3_3 8 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61
  241 (Polychromatic418967fa.accept_17_7_10_3_1_1421 7 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 61 241 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 61 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 241 (accept_3_3 5 61 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 61 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 241
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 61 241 (accept_3_3 2 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61
  241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 61 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 241 (allA_succ_of_accept
  59 60 241 (accept_3_3 59 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 241
  (Polychromatic418967fa.accept_9_4_6_7_1_286 58 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 60 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 241 (accept_3_3 56 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 60 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 241 (Polychromatic418967fa.accept_13_2_8_7_1_2424
  54 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 241 (accept_3_3 53
  60 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 241
  (Polychromatic418967fa.accept_16_4_12_1_1_1204 52 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 60 241 (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 241 (accept_3_3 50 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 60 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 48
  60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 241 (accept_3_3 47 60
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 241
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 60 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 241 (accept_3_3 44 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 60 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 241 (Polychromatic418967fa.accept_13_3_8_7_1_4135
  42 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 241 (accept_3_3 41
  60 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 241
  (Polychromatic418967fa.accept_9_4_6_7_1_286 40 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 60 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 241 (accept_3_3 38 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 60 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36
  60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 241 (accept_3_3 35 60
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 60 241 (Polychromatic418967fa.accept_25_8_10_16_1_14483 33 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 241 (accept_3_3 32 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 60 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 30
  60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 241 (accept_3_3 29 60
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 241
  (Polychromatic418967fa.accept_9_1_6_7_1_285 28 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 60 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 241 (accept_3_3 26 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 60 241 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 60 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 241
  (Polychromatic418967fa.accept_16_8_12_1_1_7720 24 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 241 (accept_3_3 23 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 241 (accept_3_3 20 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 60 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 241
  (Polychromatic418967fa.accept_16_2_12_1_1_3086 18 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 241 (accept_3_3 17 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 241 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 241 (accept_3_3 14 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 241 (accept_3_3 11 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 241 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 241 (accept_3_3 8 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 241 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 60 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 241 (accept_3_3 5 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  241 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 60 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 241 (accept_3_3 2 60 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 241 (allA_of_3_1 59 59 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 241
  (allA_succ_of_accept 57 58 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 58 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 241 (accept_3_3 56 58 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 54
  58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 241 (accept_3_3 53 58
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 241
  (Polychromatic418967fa.accept_12_4_10_1_1_706 52 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 241 (accept_3_3 50 58 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 48
  58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 241 (accept_3_3 47 58
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 241 (Polychromatic418967fa.accept_9_1_4_7_1_7
  46 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 241 (accept_3_3 44 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 241 (accept_3_3 41 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 58 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 241 (accept_3_3 38 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 241 (accept_3_3 35 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 58 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 241 (accept_3_3 32 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 241 (accept_3_3 29 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 58 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 241 (accept_3_3 26 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 241 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 241 (accept_3_3 23 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 58 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 241 (accept_3_3 20 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 58 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 241 (accept_3_3 17 58 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 58 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 241 (accept_3_3 14 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 241 (accept_3_3 11 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 58 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 241 (accept_3_3 8 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 58 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 241 (accept_3_3 5 58 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 58 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 241 (accept_3_3 2 58 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  58 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 241 (allA_succ_of_accept 56 57 241
  (accept_3_3 56 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 241
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 241 (accept_3_3 53 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 51
  57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 241 (accept_3_3 50 57
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 241
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 241 (Polychromatic418967fa.accept_17_14_6_3_1_2362 48 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 241 (accept_3_3 47 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 57 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 241 (Polychromatic418967fa.accept_11_1_2_10_1_1426
  45 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 241 (accept_3_3 44
  57 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 241
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 241 (accept_3_3 41 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 39
  57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 241 (accept_3_3 38 57
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 241 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 241 (accept_3_3 35 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 241 (accept_3_3 32 57
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 241
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 241 (accept_3_3 29 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 241 (Polychromatic418967fa.accept_12_3_9_1_1_290
  27 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 241 (accept_3_3 26
  57 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 241 (accept_3_3 23 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 241 (Polychromatic418967fa.accept_16_5_9_1_1_2070
  21 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 241 (accept_3_3 20
  57 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 241 (accept_3_3 17 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 241 (accept_3_3 14 57
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 241
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 241 (accept_3_3 11 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 9
  57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 241 (accept_3_3 8 57 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 241 (Polychromatic418967fa.accept_21_7_15_10_1_1368
  7 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 241 (accept_3_3 5 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 241 (accept_3_3 2 57 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 57 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 241 (allA_of_3_1 56 56 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 241
  (allA_succ_of_accept 54 55 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 241 (accept_3_3 53 55 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 241 (Polychromatic418967fa.accept_14_10_13_3_1_2552 52 55 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 241 (accept_3_3 50 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 241 (accept_3_3 47 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 241
  (Polychromatic418967fa.accept_19_7_17_13_1_9166 45 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 241 (accept_3_3 44 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 241 (Polychromatic418967fa.accept_13_4_3_7_1_2515 43 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 241 (accept_3_3 41 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 55 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 241 (accept_3_3 38 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 241 (accept_3_3 35 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 241 (accept_3_3 32 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 241 (accept_3_3 29 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 55 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 241
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 241 (accept_3_3 26 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 241 (accept_3_3 23 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 241 (accept_3_3 20 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 241 (accept_3_3 17 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 55 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 241 (accept_3_3 14 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 241 (accept_3_3 11 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 241 (accept_3_3 8 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 55 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 241 (accept_3_3 5 55 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 55 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 241 (accept_3_3 2 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  241 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 55 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 55 241))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 241
  (allA_succ_of_accept 53 54 241 (accept_3_3 53 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  54 241 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 241 (accept_3_3 50 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 241 (Polychromatic418967fa.accept_19_11_16_13_1_4853 49 54 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 241
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 48 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 241 (accept_3_3 47 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 241 (Polychromatic418967fa.accept_20_6_14_1_1_8896 46 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 241 (accept_3_3 44 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 241
  (Polychromatic418967fa.accept_22_20_10_21_1_9863 42 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 54 241 (accept_3_3 41 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 241 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 54 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 54 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 241 (accept_3_3 38 54 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37
  54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 241 (accept_3_3 35 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 241 (Polychromatic418967fa.accept_13_8_2_7_1_2452 34 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 241 (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 54 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 241 (accept_3_3 32 54 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 241 (accept_3_3 29 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 241 (Polychromatic418967fa.accept_22_6_10_21_1_14482 28 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 241 (accept_3_3 26 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 54 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 241
  (Polychromatic418967fa.accept_21_3_12_10_1_3885 24 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 241 (accept_3_3 23 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 241 (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 241 (accept_3_3 20 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 241
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 241 (accept_3_3 17 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 241 (accept_3_3 14 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 241 (Polychromatic418967fa.accept_20_13_14_1_1_5869 13 54 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 241
  (Polychromatic418967fa.accept_19_12_16_13_1_9123 12 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 241 (accept_3_3 11 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 241 (Polychromatic418967fa.accept_15_10_9_1_1_3688 10 54 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 241 (accept_3_3 8 54 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 241
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 241 (accept_3_3 5 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  241 (Polychromatic418967fa.accept_29_4_25_9_1_14481 4 54 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 241 (accept_3_3 2 54 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 54 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 241 (allA_of_3_1 53 53 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 241 (allA_succ_of_accept 51 52 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 241 (accept_3_3 50 52 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 241 (Polychromatic418967fa.accept_10_9_2_1_1_840
  49 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 241
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 241 (accept_3_3 47 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 241 (accept_3_3 44 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 52 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 241
  (Polychromatic418967fa.accept_11_9_8_10_1_934 42 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 241 (accept_3_3 41 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 241 (Polychromatic418967fa.accept_15_10_7_1_1_3686 40 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 241 (accept_3_3 38 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 52 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 241 (accept_3_3 35 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 241 (accept_3_3 32 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 31 52 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 241
  (Polychromatic418967fa.accept_16_14_4_1_1_3049 30 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 241 (accept_3_3 29 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 241 (Polychromatic418967fa.accept_16_12_4_1_1_1257 28 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 241 (accept_3_3 26 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 241 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 52 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 241
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 24 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 241 (accept_3_3 23 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 241 (accept_3_3 20 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 52 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 241
  (Polychromatic418967fa.accept_19_18_14_13_1_6341 18 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 52 241 (accept_3_3 17 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 52 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 52 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 241 (accept_3_3 14 52 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13
  52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 241
  (Polychromatic418967fa.accept_16_12_4_1_1_1257 12 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 241 (accept_3_3 11 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 241 (accept_3_3 8 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 241 (Polychromatic418967fa.accept_14_7_10_3_1_1034 7 52 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 241 (accept_3_3 5 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  241 (Polychromatic418967fa.accept_18_4_16_7_1_1873 4 52 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 241 (accept_3_3 2 52 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 241 (Polychromatic418967fa.accept_18_1_16_7_1_2897 1 52 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  241)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 241 (allA_succ_of_accept 50 51 241 (accept_3_3
  50 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 241
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 241 (accept_3_3 47 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 241 (Polychromatic418967fa.accept_12_9_3_1_1_303
  45 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 241 (accept_3_3 44
  51 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 241 (accept_3_3 41 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 39
  51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 241 (accept_3_3 38 51
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 241
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 51 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 241 (accept_3_3 35 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 51 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 33
  51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 241 (accept_3_3 32 51
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 241
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 51 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 241 (accept_3_3 29 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 51 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 27
  51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 241 (accept_3_3 26 51
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 241
  (Polychromatic418967fa.accept_11_3_7_10_1_180 25 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 51 241 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 241 (accept_3_3 23 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 51 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 241 (accept_3_3 20 51
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 51 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 241 (accept_3_3 17 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 51 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 241 (accept_3_3 14 51
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 51 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 241 (accept_3_3 11 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 51 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 241 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 241 (accept_3_3 8 51 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 241 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7
  51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 241 (accept_3_3 5 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 241 (accept_3_3 2 51 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 51 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 241)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 241 (allA_of_3_1 50 50 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 241
  (allA_succ_of_accept 48 49 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 241 (accept_3_3 47 49 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 49 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 241 (Polychromatic418967fa.accept_10_5_9_1_1_187
  45 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 241 (accept_3_3 44
  49 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 241
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 43 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 49 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 241 (accept_3_3 41 49 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 241 (Polychromatic418967fa.accept_18_4_13_7_1_5395 40 49 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 241 (accept_3_3 38 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 241 (Polychromatic418967fa.accept_19_17_11_13_1_4840 36 49 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 241 (accept_3_3 35 49 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 241 (Polychromatic418967fa.accept_13_8_10_7_1_1702 34 49
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 241 (accept_3_3 32 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 241 (Polychromatic418967fa.accept_17_14_15_3_1_4618 31 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 241 (accept_3_3 29 49 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 241
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 241 (accept_3_3 26 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 241 (accept_3_3 23 49 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 241 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 49 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 241 (accept_3_3 20 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 241 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 49 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 241 (accept_3_3 17 49 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 241 (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 49 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 241 (accept_3_3 14 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 241 (Polychromatic418967fa.accept_21_13_7_10_1_8599 13 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 241 (accept_3_3 11 49 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 241
  (Polychromatic418967fa.accept_21_9_7_10_1_3907 9 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 241 (accept_3_3 8 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  241 (Polychromatic418967fa.accept_19_7_11_13_1_11853 7 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 241 (accept_3_3 5 49 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 49 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 241 (accept_3_3 2 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 241))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 241 (allA_succ_of_accept 47 48 241
  (accept_3_3 47 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 46 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 241 (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 48 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 241 (accept_3_3 44 48 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 48 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 42
  48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 241 (accept_3_3 41 48
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 241
  (Polychromatic418967fa.accept_9_4_3_7_1_296 40 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 48 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 241 (accept_3_3 38 48 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 48 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 241 (Polychromatic418967fa.accept_15_6_3_1_1_3678
  36 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 241 (accept_3_3 35
  48 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 241
  (Polychromatic418967fa.accept_13_8_9_7_1_530 34 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 48 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 241 (accept_3_3 32 48 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 48 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 30
  48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 241 (accept_3_3 29 48
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 241 (Polychromatic418967fa.accept_9_1_3_7_1_6
  28 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 48 241
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 48 241 (accept_3_3 26 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  48 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 48 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 48 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 241 (accept_3_3 23 48 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 48 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 241
  (Polychromatic418967fa.accept_13_8_9_7_1_530 21 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 48 241 (accept_3_3 20 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  48 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 48 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 48 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 241 (accept_3_3 17 48 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 48 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 48 241 (accept_3_3 14 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  48 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 48 241 (Polychromatic418967fa.accept_21_12_6_10_1_14480 12 48 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 241 (accept_3_3 11 48 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 48 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 48 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 48 241 (accept_3_3 8 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48
  241 (Polychromatic418967fa.accept_20_7_8_1_1_5856 7 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 48 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 48 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 241 (accept_3_3 5 48 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 48 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48 241
  (Polychromatic418967fa.accept_10_3_8_1_1_182 3 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 241 (accept_3_3 2 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48
  241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 241)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 241 (allA_of_3_1 47 47 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 241 (allA_succ_of_accept 45 46 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 241 (accept_3_3 44 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 46 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 241 (accept_3_3 41 46 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 46 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 241 (accept_3_3 38 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 46 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 241 (accept_3_3 35 46 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 46 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 241 (accept_3_3 32 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 46 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 241 (accept_3_3 29 46 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 46 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 241 (accept_3_3 26 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 46 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 241 (accept_3_3 23 46 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 46 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 241 (accept_3_3 20 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 241 (Polychromatic418967fa.accept_19_18_8_13_1_6303 18 46 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 241 (accept_3_3 17 46 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 46 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 241 (accept_3_3 14 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 46 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 241 (accept_3_3 11 46 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 241 (Polychromatic418967fa.accept_22_10_2_21_1_11468 10 46 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 241 (accept_3_3 8 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 46 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 241 (accept_3_3 5 46 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 46 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 241 (accept_3_3 2 46 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 46
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  241)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 241 (allA_succ_of_accept 44 45 241 (accept_3_3 44 45
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 241
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 43 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 45 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 241 (accept_3_3 41 45 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  39 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 241 (accept_3_3 38
  45 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 241
  (Polychromatic418967fa.accept_16_5_13_1_1_2084 37 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 45 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 45 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 241 (accept_3_3 35 45 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 45 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 241
  (Polychromatic418967fa.accept_21_12_3_10_1_8575 33 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 241 (accept_3_3 32 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  45 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 45 241 (Polychromatic418967fa.accept_13_4_6_7_1_2471 30 45 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 241 (accept_3_3 29 45 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 241 (accept_3_3 26 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  45 241 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 241 (accept_3_3 23 45 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 45 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 241
  (Polychromatic418967fa.accept_16_5_13_1_1_2084 21 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 241 (accept_3_3 20 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  45 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 241 (Polychromatic418967fa.accept_21_18_3_10_1_8534 18 45 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 241 (accept_3_3 17 45 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 241 (accept_3_3 14 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 45 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 241 (accept_3_3 11 45 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 45 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 241
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 241 (accept_3_3 8 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  241 (Polychromatic418967fa.accept_21_7_3_10_1_13044 7 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 45 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 241 (accept_3_3 5 45 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 241 (accept_3_3 2 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45
  241 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 45 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 241))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 241 (allA_of_3_1 44 44 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 43 241 (allA_succ_of_accept 42 43 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 241 (accept_3_3 41 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 43 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 241 (accept_3_3 38 43 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 43 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 241
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 241 (accept_3_3 35 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 43 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 241 (accept_3_3 32 43 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 241 (Polychromatic418967fa.accept_16_15_11_1_1_7767 31 43 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 241 (accept_3_3 29 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 241 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 43 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 241 (accept_3_3 26 43 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 43 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 241
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 241 (accept_3_3 23 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 241 (Polychromatic418967fa.accept_25_21_18_16_1_14479 21 43 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 241 (accept_3_3 20 43 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 241 (accept_3_3 17 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 241 (Polychromatic418967fa.accept_16_15_11_1_1_7767 15 43 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 241 (accept_3_3 14 43 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 241 (Polychromatic418967fa.accept_20_13_3_1_1_3065 13 43
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 241 (accept_3_3 11 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 43 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 241 (accept_3_3 8 43 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 241 (Polychromatic418967fa.accept_19_7_5_13_1_3493 7 43 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 241 (accept_3_3 5 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 43 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 43 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 241 (accept_3_3 2 43 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 241 (Polychromatic418967fa.accept_17_1_9_3_1_7161 1 43 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 241))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 241
  (allA_succ_of_accept 41 42 241 (accept_3_3 41 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 241 (accept_3_3 38 42 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 42 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 241 (accept_3_3 35 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 34 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 42 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 241 (accept_3_3 32 42 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 241 (accept_3_3 29 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 241 (accept_3_3 26 42 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 241 (Polychromatic418967fa.accept_16_9_10_1_1_2998 25 42 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 241
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 241 (accept_3_3 23 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 241 (accept_3_3 20 42 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 241
  (Polychromatic418967fa.accept_25_18_17_16_1_14478 18 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 42 241 (accept_3_3 17 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 42 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 241 (accept_3_3 14 42 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13
  42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 241 (accept_3_3 11 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 42 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 241 (accept_3_3 8 42 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 241 (accept_3_3 5 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  241 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 42 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 241 (accept_3_3 2 42 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 241)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 241
  (allA_of_3_1 41 41 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 241 (allA_succ_of_accept 39 40 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 241 (accept_3_3 38 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 241 (accept_3_3 35 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 40 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 241 (accept_3_3 32 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 241 (Polychromatic418967fa.accept_16_15_8_1_1_9959 31 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 241 (accept_3_3 29 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 40 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 241 (accept_3_3 26 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 241 (accept_3_3 23 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 40 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 241 (accept_3_3 20 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 241 (Polychromatic418967fa.accept_17_1_6_3_1_4700 18 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 241 (accept_3_3 17 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 40 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 241 (accept_3_3 14 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 241 (accept_3_3 11 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 40 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 241 (accept_3_3 8 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 40 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 241 (accept_3_3 5 40 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 241 (Polychromatic418967fa.accept_16_4_8_1_1_5257 4 40 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 241 (accept_3_3 2 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 40 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 241)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 241 (allA_succ_of_accept 38 39 241 (accept_3_3
  38 39 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 241
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 241 (accept_3_3 35 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 33
  39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 241 (accept_3_3 32 39
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 241
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 39 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 241 (accept_3_3 29 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 39 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 27
  39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 241 (accept_3_3 26 39
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 241
  (Polychromatic418967fa.accept_10_5_9_1_1_187 25 39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 241 (accept_3_3 23 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 241 (Polychromatic418967fa.accept_12_9_3_1_1_303
  21 39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 241 (accept_3_3 20
  39 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 241
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 39 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 241 (accept_3_3 17 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 39 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 241 (accept_3_3 14 39
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 39 241 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 241 (accept_3_3 11 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 39 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 241 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 241 (accept_3_3 8 39 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365
  7 39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 241 (accept_3_3 5 39 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 241 (Polychromatic418967fa.accept_21_3_18_10_1_10020 3 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 241 (accept_3_3 2 39 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 39 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 241))))))))))))))))))))))))))))))))))))))) (allB_succ 38 241
  (allA_of_3_1 38 38 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 241 (allA_succ_of_accept 36 37 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 241 (accept_3_3 35 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 37 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 241 (accept_3_3 32 37 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 37 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 241 (accept_3_3 29 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 37 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 241 (accept_3_3 26 37 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 241 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 37 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 241 (accept_3_3 23 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 37 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 241 (accept_3_3 20 37 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 37 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 241
  (Polychromatic418967fa.accept_13_5_11_7_1_559 18 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 241 (accept_3_3 17 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 241 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 37 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 241 (accept_3_3 14 37 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 241 (accept_3_3 11 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 241 (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 241 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 37 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 241 (accept_3_3 8 37 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 241 (Polychromatic418967fa.accept_21_7_16_10_1_1349 7 37 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 241 (accept_3_3 5 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  241 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 37 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 37 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 241 (accept_3_3 2 37 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 241))))))))))))))))))))))))))))))))))))) (allB_succ 36 241
  (allA_succ_of_accept 35 36 241 (accept_3_3 35 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 241 (Polychromatic418967fa.accept_13_8_10_7_1_1702 34 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 241 (accept_3_3 32 36 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 241 (Polychromatic418967fa.accept_17_14_2_3_1_7172 31 36 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 241 (accept_3_3 29 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 241 (Polychromatic418967fa.accept_16_12_4_1_1_1257 28 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 36 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 241 (accept_3_3 26 36 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 241
  (Polychromatic418967fa.accept_15_9_6_1_1_493 24 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 241 (accept_3_3 23 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 241 (accept_3_3 20 36 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 241 (accept_3_3 17 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 36 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 241 (accept_3_3 14 36 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 36 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 241 (accept_3_3 11 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 241 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 241 (accept_3_3 8 36 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 36 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 241
  (Polychromatic418967fa.accept_19_6_17_13_1_2323 6 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 241 (accept_3_3 5 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 36 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 36 241 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 36 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 241 (accept_3_3 2 36 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 36 241 (Polychromatic418967fa.accept_17_1_2_3_1_4668 1 36 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 241)))))))))))))))))))))))))))))))))))) (allB_succ 35 241
  (allA_of_3_1 35 35 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 241 (allA_succ_of_accept 33 34 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 241 (accept_3_3 32 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 34 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 241 (accept_3_3 29 34 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 34 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 241 (accept_3_3 26 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 34 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 241 (accept_3_3 23 34 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 241 (Polychromatic418967fa.accept_13_9_8_7_1_1073 22 34 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 241 (accept_3_3 20 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 34 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 241 (accept_3_3 17 34 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 34 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 241 (accept_3_3 14 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 241 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 34 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 241 (accept_3_3 11 34 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 241 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 34
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 241 (accept_3_3 8 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 241 (Polychromatic418967fa.accept_16_6_2_1_1_4081 6 34 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 241 (accept_3_3 5 34 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 34 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 241 (accept_3_3 2 34 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 241 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1
  34 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 241))))))))))))))))))))))))))))))))))
  (allB_succ 33 241 (allA_succ_of_accept 32 33 241 (accept_3_3 32 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 33 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 33 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 241 (accept_3_3 29 33 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  33 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 241 (accept_3_3 26 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 241 (Polychromatic418967fa.accept_22_3_11_21_1_14477 25 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 241 (Polychromatic418967fa.accept_17_7_16_3_1_4660 24 33 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 241 (accept_3_3 23 33 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 33 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 241 (accept_3_3 20 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 33 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 241 (accept_3_3 17 33 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 241 (accept_3_3 14 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 241 (accept_3_3 11 33 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 241 (accept_3_3 8 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  241 (Polychromatic418967fa.accept_17_7_16_3_1_4660 7 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 33 241 (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 33 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 241 (accept_3_3 5 33 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 241 (accept_3_3 2 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33
  241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 33 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 241))))))))))))))))))))))))))))))))) (allB_succ 32 241 (allA_of_3_1 32 32 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 31 241 (allA_succ_of_accept 30 31 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 241 (accept_3_3 29 31 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28
  31 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 241
  (Polychromatic418967fa.accept_16_11_15_1_1_2074 27 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 241 (accept_3_3 26 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 241 (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 241 (accept_3_3 23 31 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 241 (accept_3_3 20 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 241 (accept_3_3 17 31 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 241 (Polychromatic418967fa.accept_19_16_12_13_1_4843 16 31 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 241 (accept_3_3 14 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 241 (Polychromatic418967fa.accept_22_13_9_21_1_9862 13 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 31 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 241 (accept_3_3 11 31 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 241
  (Polychromatic418967fa.accept_25_9_6_16_1_14476 9 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 241 (accept_3_3 8 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  241 (Polychromatic418967fa.accept_20_7_11_1_1_5840 7 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 31 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 241 (accept_3_3 5 31 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 241 (Polychromatic418967fa.accept_18_4_13_7_1_5395 4 31 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 241 (accept_3_3 2 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31
  241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 31 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 241))))))))))))))))))))))))))))))) (allB_succ 30 241 (allA_succ_of_accept 29 30 241 (accept_3_3 29 30 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 28
  30 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 30 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 30 241 (accept_3_3 26 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  30 241 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 30 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 30 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 241 (accept_3_3 23 30 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 30 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 30 241
  (Polychromatic418967fa.accept_17_4_13_3_1_7166 21 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 30 241 (accept_3_3 20 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  30 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 30 241 (Polychromatic418967fa.accept_21_18_9_10_1_2571 18 30 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 241 (accept_3_3 17 30 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 30 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 30 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 30 241 (accept_3_3 14 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  30 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 30 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 30 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 241 (accept_3_3 11 30 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 30 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 241
  (Polychromatic418967fa.accept_11_9_8_10_1_934 9 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 241 (accept_3_3 8 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30
  241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 30 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 30 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 241 (accept_3_3 5 30 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 30 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 30 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 241 (accept_3_3 2 30 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  30 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 241))))))))))))))))))))))))))))))
  (allB_succ 29 241 (allA_of_3_1 29 29 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 241
  (allA_succ_of_accept 27 28 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 241 (accept_3_3 26 28 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 28 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 28 241 (accept_3_3 23 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  28 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 28 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 241 (accept_3_3 20 28 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 28 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 241
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 241 (accept_3_3 17 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  28 241 (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 241 (accept_3_3 14 28 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 28 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 28 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 241 (accept_3_3 11 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 241 (accept_3_3 8 28 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 241 (Polychromatic418967fa.accept_19_7_9_13_1_4836 7 28 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 241 (accept_3_3 5 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 28 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 28 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 241 (accept_3_3 2 28 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 28 241 (Polychromatic418967fa.accept_21_1_7_10_1_2596 1 28 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 241)))))))))))))))))))))))))))) (allB_succ 27 241
  (allA_succ_of_accept 26 27 241 (accept_3_3 26 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  27 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 27 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 27 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 241 (accept_3_3 23 27 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 241 (accept_3_3 20 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 241 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 241 (accept_3_3 17 27 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 241
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 241 (accept_3_3 14 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 241 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 241 (Polychromatic418967fa.accept_16_12_11_1_1_4088 12 27 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 241 (accept_3_3 11 27 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 241 (accept_3_3 8 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  241 (Polychromatic418967fa.accept_17_7_10_3_1_1421 7 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 241 (accept_3_3 5 27 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 241
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 241 (accept_3_3 2 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  241 (Polychromatic418967fa.accept_19_1_8_13_1_4875 1 27 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 241))))))))))))))))))))))))))) (allB_succ 26 241 (allA_of_3_1 26 26 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 241 (allA_succ_of_accept 24 25 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 24
  25 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 241 (accept_3_3 23 25
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 241 (Polychromatic418967fa.accept_7_1_4_3_1_21
  22 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 241
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 241 (accept_3_3 20 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 25 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 241 (accept_3_3 17 25 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 25 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 241 (accept_3_3 14 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 241 (Polychromatic418967fa.accept_17_12_8_3_1_4646 12 25 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 241 (accept_3_3 11 25 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 241 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 25
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 241
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 241 (accept_3_3 8 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 25 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 241 (accept_3_3 5 25 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 25 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 241
  (Polychromatic418967fa.accept_20_3_5_1_1_4391 3 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 241 (accept_3_3 2 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 241))))))))))))))))))))))))) (allB_succ 24 241 (allA_succ_of_accept 23 24 241 (accept_3_3 23 24 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 22
  24 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 24 241 (accept_3_3 20 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  24 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 24 241 (Polychromatic418967fa.accept_13_5_11_7_1_559 18 24 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 241 (accept_3_3 17 24 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 241 (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 24 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 241
  (Polychromatic418967fa.accept_10_5_4_1_1_842 15 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 24 241 (accept_3_3 14 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  24 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 24 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 24 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 241 (accept_3_3 11 24 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 24 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 241
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 24 241 (accept_3_3 8 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24
  241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 24 241 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 24 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 241 (accept_3_3 5 24 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 24 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 241 (accept_3_3 2 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24
  241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 24 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 241)))))))))))))))))))))))) (allB_succ 23 241 (allA_of_3_1 23 23 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 241 (allA_succ_of_accept 21 22 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 241 (accept_3_3 20 22 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19
  22 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 22 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 22 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 22 241 (accept_3_3 17 22 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  22 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 22 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 22 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 241 (accept_3_3 14 22 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 22 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 22 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 22 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 22 241 (accept_3_3 11 22 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  22 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 22 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 22 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 241 (accept_3_3 8 22 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 22 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 22 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 22 241 (accept_3_3 5 22 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22
  241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 22 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 22 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 241 (accept_3_3 2 22 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 22 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 241)))))))))))))))))))))) (allB_succ 21 241 (allA_succ_of_accept
  20 21 241 (accept_3_3 20 21 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 241
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 21 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 241 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 21 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 241 (accept_3_3 17 21 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  21 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 241 (accept_3_3 14 21
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 241
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 21 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 21 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 241 (accept_3_3 11 21 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 21 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 21 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 241 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9
  21 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 241 (accept_3_3 8 21 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 241 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7
  21 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 241 (accept_3_3 5 21 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 21 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 241 (accept_3_3 2 21 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 21 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 241))))))))))))))))))))) (allB_succ 20 241 (allA_of_3_1 20 20
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 241 (allA_succ_of_accept 18 19 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 241 (accept_3_3 17 19 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 19 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 19 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 241 (accept_3_3 14 19 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 19 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 241 (accept_3_3 11 19 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 19 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 241 (accept_3_3 8 19 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 241 (Polychromatic418967fa.accept_21_7_19_10_1_8567 7 19 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 241 (accept_3_3 5 19 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 19 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 19 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 241 (accept_3_3 2 19 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 19 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 241))))))))))))))))))) (allB_succ 18 241 (allA_succ_of_accept 17
  18 241 (accept_3_3 17 18 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 241
  (Polychromatic418967fa.accept_19_16_18_13_1_4855 16 18 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 18 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 241 (accept_3_3 14 18 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 18 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 241
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 18 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 18 241 (accept_3_3 11 18 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  18 241 (Polychromatic418967fa.accept_22_10_18_21_1_8227 10 18 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 18 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 18 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 241 (accept_3_3 8 18 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 18 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 241 (accept_3_3 5 18 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18
  241 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 18 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 18 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 241 (accept_3_3 2 18 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 18 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 18 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 241)))))))))))))))))) (allB_succ 17 241 (allA_of_3_1 17 17 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 241 (allA_succ_of_accept 15 16 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 241 (accept_3_3 14 16 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 16 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 16 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 241 (accept_3_3 11 16 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 16 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 241 (accept_3_3 8 16 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  241 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 16 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 16 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 241 (accept_3_3 5 16 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 16 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 241 (accept_3_3 2 16 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  16 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 241)))))))))))))))) (allB_succ 15 241
  (allA_succ_of_accept 14 15 241 (accept_3_3 14 15 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  15 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 15 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 241 (accept_3_3 11 15 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 241 (accept_3_3 8 15 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  241 (Polychromatic418967fa.accept_19_7_15_13_1_9152 7 15 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 241 (accept_3_3 5 15 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 15 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 241 (accept_3_3 2 15 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15
  241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 15 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 241))))))))))))))) (allB_succ 14 241 (allA_of_3_1 14 14 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 13 241 (allA_succ_of_accept 12 13 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 13 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 13 241 (accept_3_3 11 13 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 13 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 13 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 13 241 (accept_3_3 8 13 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13
  241 (Polychromatic418967fa.accept_21_7_13_10_1_8604 7 13 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 13 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 241 (accept_3_3 5 13 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 13 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 13 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 241 (accept_3_3 2 13 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13
  241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 241))))))))))))) (allB_succ 12 241 (allA_succ_of_accept 11 12 241 (accept_3_3 11 12 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 12 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 12 241 (accept_3_3 8 12 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12
  241 (Polychromatic418967fa.accept_17_7_12_3_1_4693 7 12 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 12 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 12 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 241 (accept_3_3 5 12 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 12 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 241
  (Polychromatic418967fa.accept_10_3_2_1_1_839 3 12 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 241 (accept_3_3 2 12 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 241)))))))))))) (allB_succ 11 241 (allA_of_3_1 11 11 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 241 (allA_succ_of_accept 9 10 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 241 (accept_3_3 8 10 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 10 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 241 (accept_3_3 5 10 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 10 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 241 (accept_3_3 2 10 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 241 (Polychromatic418967fa.accept_19_1_10_13_1_4880 1 10 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 241)))))))))) (allB_succ 9 241 (allA_succ_of_accept 8 9 241
  (accept_3_3 8 9 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 241
  (Polychromatic418967fa.accept_15_7_9_1_1_473 7 9 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 241 (accept_3_3 5 9 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 9
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 241 (accept_3_3 2 9 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 9
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 241))))))))) (allB_succ 8 241
  (allA_of_3_1 8 8 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 241 (allA_succ_of_accept 6 7 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 241 (accept_3_3 5 7 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 241
  (Polychromatic418967fa.accept_10_4_7_1_1_471 4 7 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 7 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 241 (accept_3_3 2 7 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 241 (Polychromatic418967fa.accept_19_1_7_13_1_4813 1 7 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 241))))))) (allB_succ 6 241 (allA_succ_of_accept 5 6 241
  (accept_3_3 5 6 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 6 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 241 (accept_3_3 2 6 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 6 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 241)))))) (allB_succ 5 241 (allA_of_3_1 5 5 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 241 (allA_succ_of_accept 3 4 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 241 (accept_3_3 2 4 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 241)))) (allB_succ 3 241 (allA_succ_of_accept 2 3 241 (accept_3_3 2 3 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 3 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 241))) (allB_succ 2 241 (allA_of_3_1 2 2 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


