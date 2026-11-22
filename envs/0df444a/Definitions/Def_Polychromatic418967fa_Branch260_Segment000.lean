-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch260_Segment000
-- name    : Polychromatic418967fa_Branch260_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:43:12.008796+00:00
-- url     : https://prove2.me/theorems/6ebc3028-8db4-47f9-bb2c-477e29f37c31
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

def Polychromatic418967fa.branch_260_segment_000 : allB 125 260 :=
  allB_succ 124 260 (allA_of_3_0 124 124 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 123 260
  (allA_succ_of_accept 122 123 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 122 123 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 123 260 (accept_3_2 121 123 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 123 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 120 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 123 260 (accept_3_2 118 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 123 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 117 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 123 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 116 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 123 260 (accept_3_2 115 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 123 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 114 123
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 123 260 (accept_3_2 112 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 123 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 111 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 123 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 110 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 123 260 (accept_3_2 109 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 108 123
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 123 260 (accept_3_2 106 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 123 260 (Polychromatic418967fa.accept_16_9_11_4_1_3194 105 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 123 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 104 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 260 (accept_3_2 103 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 123
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 123 260 (accept_3_2 100 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 123 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 99 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 123 260 (Polychromatic418967fa.accept_15_8_3_5_1_608 98 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 260 (accept_3_2 97 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 96 123 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 123 260 (accept_3_2 94 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 123 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 123 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 92 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 260 (accept_3_2 91 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 260 (accept_3_2 88 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 123 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 123 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 260 (accept_3_2 85 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 123 260 (accept_3_2 82 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 123 260 (Polychromatic418967fa.accept_15_6_3_5_1_607 81 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 123 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 260 (accept_3_2 79 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 260 (accept_3_2 76 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 123 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 123 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 260 (accept_3_2 73 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 260 (Polychromatic418967fa.accept_16_8_11_4_1_3290 72 123 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 123 260 (accept_3_2 70 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 123 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 69 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 123 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 260 (accept_3_2 67 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 123 260 (accept_3_2 64 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 123 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 123 260 (Polychromatic418967fa.accept_15_2_3_5_1_2991 62 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 260 (accept_3_2 61 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 60 123
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 260 (accept_3_2 58 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 123 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 123 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 260 (accept_3_2 55 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 260 (accept_3_2 52 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 260 (Polychromatic418967fa.accept_15_6_3_5_1_607 51 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 123 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 260 (accept_3_2 49 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 260 (accept_3_2 46 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 260 (Polychromatic418967fa.accept_16_12_11_4_1_1359 44 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 260 (accept_3_2 43 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 260 (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 123
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 260 (accept_3_2 40 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 260 (accept_3_2 37 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 260 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 260 (accept_3_2 34 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 260 (accept_3_2 31 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 260 (accept_3_2 28 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 260 (Polychromatic418967fa.accept_22_5_13_18_1_12746 27 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 260 (accept_3_2 25 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 123 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 260 (accept_3_2 22 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 260 (accept_3_2 19 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 260 (accept_3_2 16 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 260 (accept_3_2 13 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 260 (accept_3_2 10 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 260 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 260 (Polychromatic418967fa.accept_15_8_3_5_1_608 8 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 260 (accept_3_2 7 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 123 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 260 (accept_3_2 4 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 123 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 260 (accept_3_2 1 123 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 122 260 (allA_succ_of_accept 121 122 260 (accept_3_2 121 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 122 260 2 60 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 122 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 119 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 122 260 2 59 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 122 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 117 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 122 260 2 58 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 122 260 (accept_3_2 115 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 122 260 2 57 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 122 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 113 122 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 122 260 2 56 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 122 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 111 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 122 260 2 55 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 122 260 (accept_3_2 109 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 122 260 2 54 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 122 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 107 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 122 260 2 53 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 122 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 105 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 122 260 2 52 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 122 260 (accept_3_2 103 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 122 260 2 51 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 122 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 122 260 2 50 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 122 260
  (Polychromatic418967fa.accept_19_4_8_13_1_7802 99 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 122 260 2 49 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 122 260 (accept_3_2 97 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 122 260 2 48 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 122 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 122 260 2 47 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 122 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 122 260 2 46 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 122 260 (accept_3_2 91 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 122 260 2 45 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 122 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 260 2 44 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 87 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 260 2 43 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 260 (accept_3_2 85 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 260 2 42 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 260 2 41 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 122 260 2 40 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 122 260 (accept_3_2 79 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 260 2 39 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 260 2 38 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 260 2 37 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 260 (accept_3_2 73 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 260 2 36 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 122 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 260 2 35 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 260 2 34 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 260 (accept_3_2 67 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 260 2 33 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 260 2 32 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 260
  (Polychromatic418967fa.accept_15_3_2_5_1_2980 63 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 260 2 31 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 260 (accept_3_2 61 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 260 2 30 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 122 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 260 2 29 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 260 2 28 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 260 (accept_3_2 55 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 260 2 27 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 260 2 26 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 260 2 25 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 260 (accept_3_2 49 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 260 2 24 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 260 2 23 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 260
  (Polychromatic418967fa.accept_21_3_17_8_1_8402 45 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 260 2 22 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 260 (accept_3_2 43 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 260 2 21 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 260 2 20 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 260 2 19 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 260 (accept_3_2 37 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 260 2 18 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 122 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 260 2 17 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 260 2 16 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 260 (accept_3_2 31 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 260 2 15 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 260 2 14 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 260
  (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 260 2 13 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 260 (accept_3_2 25 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 260 2 12 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 260 2 11 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 260 2 10 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 260 (accept_3_2 19 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 260 2 9 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 122 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 260 2 8 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 260 2 7 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 260 (accept_3_2 13 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 260 2 6 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 122 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 260 2 5 61 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 260 2 4 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 260 (accept_3_2 7 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  260 2 3 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 122 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 260 2 2 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 122 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 260 2 1 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 260 (accept_3_2 1 122 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 260 (allA_of_3_0 121 121 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 260
  (allA_succ_of_accept 119 120 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 119 120 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 120 260 2 59 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 120 260 (Polychromatic418967fa.accept_16_5_8_4_1_5418
  117 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 120 260 4 29 30 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 115 120 260 5 23 24
  52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 114 120 260 2 57
  60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 120
  260 (Polychromatic418967fa.accept_9_5_3_8_1_316 113 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 112 120 260 4 28 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 111 120 260 (Polychromatic418967fa.accept_16_15_8_4_1_1355 111 120 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 120 260 10 11 12 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 260 (accept_3_2
  109 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 120 260 4 27 30 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 120 260
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 107 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 120 260 2 53 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 105 120 260 5 21 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 120 260 4 26 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 260 (accept_3_2 103 120 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 102 120 260 2 51 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 120 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 120
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 120 260 20 5 6 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 120 260
  (Polychromatic418967fa.accept_16_3_8_4_1_3279 99 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 120 260 2 49 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 120 260 (accept_3_2 97 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 120 260 4 24 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 95 120 260 5 19 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 94 120 260 2 47 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 120 260 (Polychromatic418967fa.accept_16_13_8_4_1_3250 93 120
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 120 260 4 23 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 260 (accept_3_2 91
  120 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 120 260 10 9 12 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 120 260
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 89 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 120 260 4 22 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 120 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 120 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 120 260 2 43 60 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 120 260 5 17 24 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 120 260 4 21 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 120 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 120 260 2 41 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 120 260 (Polychromatic418967fa.accept_16_1_8_4_1_4334 81 120 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 120 260 20 4 6 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 120 260 (accept_3_2 79 120 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 120 260 2 39 60 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 120 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 120 260 4 19 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 120 260 5 15 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 120 260 2 37 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 260 (accept_3_2 73 120 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 120 260 4 18 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 120 260 (Polychromatic418967fa.accept_16_7_8_4_1_689 71 120 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 260 10 7 12 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 120 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 69 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 120 260 4 17 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 120 260 (accept_3_2 67 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 260 2 33 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 120 260 5 13 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 120 260 4 16 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 260 (Polychromatic418967fa.accept_16_15_8_4_1_1355 63 120
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 120 260 2 31 60 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 260 (accept_3_2 61
  120 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 260 20 3 6 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 120 260 2 29 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 120 260 (Polychromatic418967fa.accept_16_9_8_4_1_1354 57 120 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 120 260 4 14 30 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 120 260 5 11 24 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 120 260 2 27 60 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 260
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 53 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 120 260 4 13 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 120 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 120 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 260 10 5 12 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 260 (accept_3_2 49 120 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 260 4 12 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 47
  120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 260 2 23 60 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 260 5 9 24 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 260 4 11 30 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 260
  (accept_3_2 43 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 260 2 21 60 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 260 20 2 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 120 260 (Polychromatic418967fa.accept_16_7_8_4_1_689 39 120 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 260 2 19 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 260 (accept_3_2 37 120 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 260 4 9 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 120 260 5 7 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 120 260 2 17 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 33
  120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 260 4 8 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 260 (accept_3_2 31
  120 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 260 10 3 12 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 260 4 7 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 120 260 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 120 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 260 2 13 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 120 260 5 5 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 260 4 6 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 23
  120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 260 2 11 60 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 260
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 21 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 260 20 1 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 260 (accept_3_2 19 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  120 260 2 9 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 260 (Polychromatic418967fa.accept_16_1_8_4_1_4334 17 120 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 260 4 4 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 260 5 3 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 260 2 7 60 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 260 (accept_3_2 13 120 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 260 4 3 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 11
  120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 260 10 1 12 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 260
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 260 4 2 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 260 (accept_3_2 7 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120
  260 2 3 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120
  260 5 1 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 120
  260 4 1 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  120 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 120 260 2 1 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 120 260 (accept_3_2 1 120 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 260 (allA_succ_of_accept 118 119 260 (accept_3_2 118 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 119 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 260 (Polychromatic418967fa.accept_21_11_14_8_1_5256 116
  119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 260 (accept_3_2 115
  119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 114 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 113 119 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 260 (accept_3_2 112 119 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 110 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 119 260 (accept_3_2 109 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 119 260 (Polychromatic418967fa.accept_16_12_7_4_1_687 108 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 119 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 107 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 260 (accept_3_2 106 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 119
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 104 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 119 260 (accept_3_2 103 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 119 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 119 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 101 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 260 (accept_3_2 100 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 119 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 98 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 119 260 (accept_3_2 97 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 119 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 119 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 260 (accept_3_2 94 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 260
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 92 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 260 (accept_3_2 91 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 90 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 260 (Polychromatic418967fa.accept_21_5_14_8_1_6818 89 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 260 (accept_3_2 88 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 119 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 260 (accept_3_2 85 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 83 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 260 (accept_3_2 82 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 260
  (Polychromatic418967fa.accept_21_17_14_8_1_11452 80 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 119 260 (accept_3_2 79 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 119 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 119 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 119 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 260 (accept_3_2 76 119 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75
  119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 74 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 260 (accept_3_2 73 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 260 (Polychromatic418967fa.accept_16_8_7_4_1_2217 72 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 260 (Polychromatic418967fa.accept_11_5_9_7_1_411 71 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 260 (accept_3_2 70 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 119 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 260 (accept_3_2 67 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 260 (Polychromatic418967fa.accept_19_8_5_13_1_7800 65 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 260 (accept_3_2 64 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 119 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 62 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 260 (accept_3_2 61 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 260 (accept_3_2 58 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 260
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 56 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 260 (accept_3_2 55 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 260 (Polychromatic418967fa.accept_15_9_14_5_1_2086 54 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 260 (Polychromatic418967fa.accept_15_8_14_5_1_2089 53 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 260 (accept_3_2 52 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 260 (accept_3_2 49 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 260 (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 260 (accept_3_2 46 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 119 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 260
  (Polychromatic418967fa.accept_16_12_7_4_1_687 44 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 260 (accept_3_2 43 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 260 (accept_3_2 40 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 260
  (Polychromatic418967fa.accept_11_5_9_7_1_411 38 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 260 (accept_3_2 37 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 260 (Polychromatic418967fa.accept_15_6_14_5_1_2976 36 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 260 (accept_3_2 34 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 260 (accept_3_2 31 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 260 (Polychromatic418967fa.accept_14_1_7_8_1_2063 29 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 260 (accept_3_2 28 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 260 (accept_3_2 25 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 260 (accept_3_2 22 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 260
  (Polychromatic418967fa.accept_14_6_7_8_1_624 20 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 260 (accept_3_2 19 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 260 (Polychromatic418967fa.accept_19_18_5_13_1_15859 18 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 260 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 119 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 260 (accept_3_2 16 119 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 260 (accept_3_2 13 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 260 (accept_3_2 10 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 260
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 260 (accept_3_2 7 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 260 (accept_3_2 4 119 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 260
  (Polychromatic418967fa.accept_11_2_9_7_1_124 2 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 260 (accept_3_2 1 119 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 260 (allA_of_3_0 118 118 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 260
  (allA_succ_of_accept 116 117 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 116 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 260 (accept_3_2 115 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 117 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 114 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 260 (accept_3_2 112 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 111 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 260 (Polychromatic418967fa.accept_21_5_12_8_1_6807 110 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 260 (accept_3_2 109 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 108 117
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 260 (accept_3_2 106 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 105 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 117 260 13 8 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 117 260 (accept_3_2 103 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 117 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 102 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 117
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 260 (accept_3_2 100 117
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 117 260
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 99 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 117 260 (Polychromatic418967fa.accept_15_8_12_5_1_2987 98 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 260 (accept_3_2 97 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 117 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 96 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 260 (accept_3_2 94 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 117 260 (Polychromatic418967fa.accept_18_3_9_8_1_2977 93 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 117 260 (Polychromatic418967fa.accept_15_2_12_5_1_2107 92 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 117 260 13 7 9 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 117 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 90 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 117 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 260 (accept_3_2 88 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 117 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 260 (Polychromatic418967fa.accept_16_6_5_4_1_4330
  86 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 260 (accept_3_2 85
  117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 260
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 84 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 117 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 260 (accept_3_2 82 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 117 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 80
  117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 260 (accept_3_2 79
  117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 117 260 13 6 9 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 117 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 260 (accept_3_2 76 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 117 260 (Polychromatic418967fa.accept_17_7_15_5_1_3649 75 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 117 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 260 (accept_3_2 73 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 260 (Polychromatic418967fa.accept_16_8_5_4_1_674 72 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 260 (accept_3_2 70 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 117 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 260 (Polychromatic418967fa.accept_15_8_12_5_1_2987 68 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 260 (accept_3_2 67 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 117 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 117 260 13 5 9 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 117 260 (accept_3_2 64
  117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 260
  (Polychromatic418967fa.accept_16_15_5_4_1_6678 63 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 117 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 62 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 260 (accept_3_2 61 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 117 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59
  117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 260 (accept_3_2 58
  117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 260
  (Polychromatic418967fa.accept_8_1_5_4_1_388 57 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 117 260 (Polychromatic418967fa.accept_16_8_5_4_1_674 56 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 260 (accept_3_2 55 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 117 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 117 260 13 4 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 117 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 51 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 260 (Polychromatic418967fa.accept_19_12_3_13_1_4911 50 117
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 260 (accept_3_2 49 117
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 117 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 260 (accept_3_2 46 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 117 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 260
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 44 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 260 (accept_3_2 43 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 117 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 117 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 260 (accept_3_2 40 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 260 13 3 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 117 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 260 (accept_3_2 37 117 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 260
  (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 117 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 260 (accept_3_2 34 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 260 (Polychromatic418967fa.accept_7_4_5_1_1_418
  32 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 260 (accept_3_2 31
  117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 260
  (Polychromatic418967fa.accept_12_6_9_8_1_165 30 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 117 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 260 (accept_3_2 28 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 117 260 13 2 9 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 117 260 (accept_3_2 25 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 117 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 260 (accept_3_2 22 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 260 (accept_3_2 19 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 260 (accept_3_2 16 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 260 (Polychromatic418967fa.accept_16_15_5_4_1_6678 15 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 260 (Polychromatic418967fa.accept_21_14_12_8_1_6833 14 117 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 117 260 13 1 9 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 117 260
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 12 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 260 (accept_3_2 10 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 260 (Polychromatic418967fa.accept_15_8_12_5_1_2987
  8 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 260 (accept_3_2 7
  117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 260 (accept_3_2 4 117 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 117 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 260 (Polychromatic418967fa.accept_15_2_12_5_1_2107
  2 117 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 260 (accept_3_2 1
  117 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 260 (allA_succ_of_accept 115 116 260 (accept_3_2 115 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 116 260 2 57 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 116 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 113 116 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 116 260 4 28 29 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 116 260
  (Polychromatic418967fa.accept_11_1_6_7_1_116 111 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 116 260 2 55 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 116 260 (accept_3_2 109 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 116 260 4 27 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 116 260 (Polychromatic418967fa.accept_15_2_11_5_1_1266 107 116 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 116 260 2 53 58 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 116 260
  (Polychromatic418967fa.accept_19_10_2_13_1_9183 105 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 116 260 4 26 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 116 260 (accept_3_2 103 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 116 260 2 51 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 116 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 116 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 116 260 4 25 29 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 116 260
  (Polychromatic418967fa.accept_15_9_11_5_1_1283 99 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 116 260 2 49 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 116 260 (accept_3_2 97 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 116 260 4 24 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 116 260 (Polychromatic418967fa.accept_14_11_4_8_1_664 95 116 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 260 2 47 58 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 260
  (Polychromatic418967fa.accept_27_12_8_17_1_13900 93 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 116 260 4 23 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 116 260 (accept_3_2 91 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 260 2 45 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 116 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 260 4 22 29 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 87 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 116 260 2 43 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 116 260 (accept_3_2 85 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 260 4 21 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 83 116 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 260 2 41 58 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 260
  (Polychromatic418967fa.accept_14_11_4_8_1_664 81 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 260 4 20 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 260 (accept_3_2 79 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 260 2 39 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 260 (Polychromatic418967fa.accept_15_2_11_5_1_1266 77 116 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 260 4 19 29 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 260 2 37 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 260 (accept_3_2 73 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 260 4 18 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 260 (Polychromatic418967fa.accept_23_2_1_7_1_15858 71 116 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 260 2 35 58 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 260
  (Polychromatic418967fa.accept_15_9_11_5_1_1283 69 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 260 4 17 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 260 (accept_3_2 67 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 260 2 33 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 260 (Polychromatic418967fa.accept_19_8_2_13_1_2328 65 116 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 260 4 16 29 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 260
  (Polychromatic418967fa.accept_19_6_2_13_1_4945 63 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 116 260 2 31 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 116 260 (accept_3_2 61 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 260 4 15 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 116 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 260 2 29 58 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 260
  (Polychromatic418967fa.accept_22_13_6_18_1_12837 57 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 116 260 4 14 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 116 260 (accept_3_2 55 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 260 2 27 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 260 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 116 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 260 4 13 29 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 260
  (Polychromatic418967fa.accept_15_6_11_5_1_168 51 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 260 2 25 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 260 (accept_3_2 49 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 260 4 12 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 116 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 260 2 23 58 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 260 4 11 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 260 (accept_3_2 43 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 260 2 21 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 260 (Polychromatic418967fa.accept_21_20_11_8_1_9906 41 116 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 260 4 10 29 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 260
  (Polychromatic418967fa.accept_14_11_4_8_1_664 39 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 260 2 19 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 260 (accept_3_2 37 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 260 4 9 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 260 (Polychromatic418967fa.accept_19_16_2_13_1_13234 35 116 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 260 2 17 58 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 260 4 8 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 116 260 (accept_3_2 31 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  116 260 2 15 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 116 260 (Polychromatic418967fa.accept_19_10_2_13_1_9183 29 116 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 260 4 7 29 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 260
  (Polychromatic418967fa.accept_17_10_14_5_1_11167 27 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 116 260 2 13 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 116 260 (accept_3_2 25 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 260 4 6 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 116 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 116 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 260 2 11 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 260 (Polychromatic418967fa.accept_15_6_11_5_1_168
  21 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 116 260 4 5 29 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 116 260
  (accept_3_2 19 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 116 260 2 9 58 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 116 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 116 260 4 4 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 116 260 (Polychromatic418967fa.accept_19_15_2_13_1_10598 15 116 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 260 2 7 58 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 260 (accept_3_2 13 116 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 260 4 3 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 260 (Polychromatic418967fa.accept_14_11_4_8_1_664
  11 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 260 2 5 58 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 260
  (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 116 260 4 2 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 260 (accept_3_2 7 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116
  260 2 3 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  116 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 116 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 116 260 4 1 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 116 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 116 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 260 2 1 58 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 260 (accept_3_2 1 116 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 116
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 260 (allA_of_3_0 115 115 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 260
  (allA_succ_of_accept 113 114 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 113 114 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 114 260 2 56 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 114 260 (Polychromatic418967fa.accept_7_6_2_1_1_214
  111 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 114 260 2 55 57 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 260
  (accept_3_2 109 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 114 260 2 54 57 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 114 260
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 107 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 114 260 2 53 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 114 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 105 114 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 260 2 52 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 260 (accept_3_2 103 114 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 114 260 2 51 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 114 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 101 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 114 260 2 50 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 114 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 260 2 49 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 260 (accept_3_2 97 114 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 114 260 2 48 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 95
  114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 260 2 47 57 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 114 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 93 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 114 260 2 46 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 114 260 (accept_3_2 91 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 260 2 45 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 260 (Polychromatic418967fa.accept_15_14_9_5_1_3932 89 114 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 260 2 44 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 114 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 114 260 2 43 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 114 260 (accept_3_2 85 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 260 2 42 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 260 2 41 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 114 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 114 260 2 40 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 114 260 (accept_3_2 79 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 260 2 39 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 260 2 38 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 114 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 75 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 114 260 2 37 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 114 260 (accept_3_2 73 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 260 2 36 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 260 (Polychromatic418967fa.accept_14_1_2_8_1_655 71 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 260 2 35 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 114 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 114 260 2 34 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 260 (accept_3_2 67 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 260 2 33 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 260 2 32 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 260
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 260 2 31 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 260 (accept_3_2 61 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 260 2 30 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 260 2 29 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 260 2 28 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 260 (accept_3_2 55 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 260 2 27 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 260 (Polychromatic418967fa.accept_25_3_14_10_1_15857 53 114 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 260 2 26 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 260 2 25 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 260 (accept_3_2 49 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 260 2 24 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 260 2 23 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 260 2 22 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 260 (accept_3_2 43 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 260 2 21 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 260 2 20 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 260 2 19 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 260 (accept_3_2 37 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 260 2 18 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 260 (Polychromatic418967fa.accept_30_5_24_20_1_15856 35 114 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 260 2 17 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 260 2 16 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 260 (accept_3_2 31 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 260 2 15 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 260 2 14 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 260 2 13 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 260 (accept_3_2 25 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 260 2 12 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 260 2 11 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 260 2 10 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 260 (accept_3_2 19 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 260 2 9 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 260 2 8 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 260 2 7 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 114 260 (accept_3_2 13 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 260 2 6 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 114 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 260 2 5 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 260 2 4 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 260 (accept_3_2 7 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114
  260 2 3 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 114 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 260 2 2 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 114 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 114 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 260 2 1 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 260 (accept_3_2 1 114 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 260 (allA_succ_of_accept 112 113 260 (accept_3_2 112 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 113 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 113
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 260 (accept_3_2 109 113
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 260
  (Polychromatic418967fa.accept_15_3_8_5_1_2105 108 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 260 (Polychromatic418967fa.accept_14_9_1_8_1_2849 107 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 260 (accept_3_2 106 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 260
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 104 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 113 260 (accept_3_2 103 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 113 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 113 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 113 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 101 113
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 260 (accept_3_2 100 113
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 99 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 113 260 (Polychromatic418967fa.accept_11_10_3_7_1_2564 98 113 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 113 260 (accept_3_2 97 113 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 113 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 113 260
  (Polychromatic418967fa.accept_22_7_3_18_1_12759 95 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 113 260 (accept_3_2 94 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 113 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 113 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 113 260 (accept_3_2 91 113 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 113 260
  (Polychromatic418967fa.accept_19_14_18_13_1_7823 90 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 260 (Polychromatic418967fa.accept_15_14_8_5_1_2104 89 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 260 (accept_3_2 88 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 113 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 260 (accept_3_2 85 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 260 (accept_3_2 82 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 260
  (Polychromatic418967fa.accept_25_5_13_10_1_15855 80 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 113 260 (accept_3_2 79 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 113 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 113 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 113 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 260 (accept_3_2 76 113 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75
  113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 260 (accept_3_2 73 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 260 (Polychromatic418967fa.accept_14_2_1_8_1_650 72 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 260 (Polychromatic418967fa.accept_15_11_8_5_1_1278 71 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 260 (accept_3_2 70 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 260
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 68 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 260 (accept_3_2 67 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 260 (accept_3_2 64 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 260 (accept_3_2 61 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 260 (Polychromatic418967fa.accept_11_4_3_7_1_828 59 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 260 (accept_3_2 58 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 260 (accept_3_2 55 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 260 (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 260 (accept_3_2 52 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 260 (accept_3_2 49 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 260 (accept_3_2 46 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 260
  (Polychromatic418967fa.accept_14_2_1_8_1_650 44 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 260 (accept_3_2 43 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 260 (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 260 (accept_3_2 40 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 113 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 260 (accept_3_2 37 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 260 (Polychromatic418967fa.accept_19_17_18_13_1_9126 36 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 260 (Polychromatic418967fa.accept_14_7_1_8_1_2873 35 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 260 (accept_3_2 34 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 260
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 32 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 260 (accept_3_2 31 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 260 (accept_3_2 28 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 260
  (Polychromatic418967fa.accept_11_4_3_7_1_828 26 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 260 (accept_3_2 25 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 260 (Polychromatic418967fa.accept_14_9_1_8_1_2849 23 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 260 (accept_3_2 22 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 260 (accept_3_2 19 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 260 (Polychromatic418967fa.accept_18_17_5_8_1_1898 17 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 260 (accept_3_2 16 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 260 (accept_3_2 13 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 260 (accept_3_2 10 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 260
  (Polychromatic418967fa.accept_16_8_1_4_1_6622 8 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 260 (accept_3_2 7 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 260 (accept_3_2 4 113 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 260 (accept_3_2 1 113 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 260 (allA_of_3_0 112 112 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 260
  (allA_succ_of_accept 110 111 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 110 111 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 260 (accept_3_2 109 111 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 260 (Polychromatic418967fa.accept_15_3_6_5_1_2079 108 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 260 (accept_3_2 106 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 104 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 260 (accept_3_2 103 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 102 111
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 260 (accept_3_2 100 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 99 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 260 (Polychromatic418967fa.accept_17_13_9_5_1_6022 98 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 260 (accept_3_2 97 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 111 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 260 (accept_3_2 94 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 92 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 260 (accept_3_2 91 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 260 (accept_3_2 88 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 86 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 260 (accept_3_2 85 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 260 (Polychromatic418967fa.accept_18_12_3_8_1_6817 84 111 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 260 (accept_3_2 82 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 260 (Polychromatic418967fa.accept_17_13_9_5_1_6022 81 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 260 (Polychromatic418967fa.accept_17_12_9_5_1_799 80 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 260 (accept_3_2 79 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 111 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 260 (accept_3_2 76 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 260 (accept_3_2 73 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 260 (accept_3_2 70 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 260 (accept_3_2 67 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 260 (accept_3_2 64 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 260 (Polychromatic418967fa.accept_14_7_13_8_1_2067 63 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 260 (Polychromatic418967fa.accept_16_14_15_4_1_3268 62 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 260 (accept_3_2 61 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 111 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 260 (accept_3_2 58 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 260 (Polychromatic418967fa.accept_15_12_6_5_1_1275 57 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 260 (accept_3_2 55 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 260 (accept_3_2 52 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 260 (accept_3_2 49 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 260 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 260 (accept_3_2 46 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 260 (Polychromatic418967fa.accept_18_9_3_8_1_5419 45 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 260 (accept_3_2 43 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 260 (accept_3_2 40 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 260 (accept_3_2 37 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 260 (Polychromatic418967fa.accept_19_17_16_13_1_4900 36 111 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 260 (accept_3_2 34 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 260 (accept_3_2 31 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 260 (accept_3_2 28 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 260 (accept_3_2 25 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 260 (accept_3_2 22 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 260 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 260 (accept_3_2 19 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 260 (accept_3_2 16 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 260 (accept_3_2 13 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 260 (accept_3_2 10 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 260 (Polychromatic418967fa.accept_16_8_15_4_1_5402 8 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 260 (accept_3_2 7 111 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 111 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 260 (accept_3_2 4 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 111 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 260 (accept_3_2 1 111 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 260 (allA_succ_of_accept 109 110 260 (accept_3_2 109 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 260 2 54 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 107 110 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 260 2 53 55 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 110 260 5 21 22 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 110 260 2 52 55 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 110 260
  (accept_3_2 103 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 110 260 2 51 55 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 110 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 101 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 110 260 10 10 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 110 260 (Polychromatic418967fa.accept_19_4_15_13_1_13215 99 110 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 110 260 2 49 55 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 110 260 (accept_3_2 97 110 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 110 260 2 48 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 110 260 5 19 22 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 110 260 2 47 55 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 93 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 110 260 2 46 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 110 260 (accept_3_2 91 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 260 10 9 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 110 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 260 2 44 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 260 2 43 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 110 260 5 17 22 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 110 260 2 42 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 110 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 110 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 260 2 41 55 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 81 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 260 10 8 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 260 (accept_3_2 79 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 260 2 39 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 110 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 260 2 38 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 110 260 5 15 22 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 110 260 2 37 55 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 110 260 (accept_3_2 73
  110 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 110 260 2 36 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 110 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 71 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 110 260 10 7 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 110 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 110 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 110 260 2 34 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 110 260 (accept_3_2 67 110 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 110 260 2 33 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 110 260 5 13 22 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 110 260 2 32 55 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 260
  (Polychromatic418967fa.accept_16_15_14_4_1_6649 63 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 110 260 2 31 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 110 260 (accept_3_2 61 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 260 10 6 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 110 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 260 2 29 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 260 2 28 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 110 260 5 11 22 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 110 260 2 27 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 110 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 110 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 260 2 26 55 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 260 10 5 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 260 (accept_3_2 49 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 260 2 24 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 110 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 260 2 23 55 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 110 260 5 9 22 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 110 260 2 22 55 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 110 260 (accept_3_2 43
  110 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 110 260 2 21 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 110 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 110 260 10 4 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 110 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 110 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 110 260 2 19 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 110 260 (accept_3_2 37 110 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 110 260 2 18 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 110 260 5 7 22 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 110 260 2 17 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 260 2 16 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 260 (accept_3_2 31 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 260 10 3 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 110 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 260 2 14 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 260 2 13 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 110 260 5 5 22 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 110 260 2 12 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 110 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 110 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 260 2 11 55 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 260 10 2 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 260 (accept_3_2 19 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 260 2 9 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 110 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 260 2 8 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 110 260 5 3 22 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 110 260 2 7 55 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 260 (accept_3_2 13 110 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 260 2 6 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 260 10 1 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 110 260 (Polychromatic418967fa.accept_16_9_14_4_1_3225 9 110 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 260 2 4 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 260 (accept_3_2 7 110 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110 260 2 3 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 110 260 5 1 22 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 110 260 2 2 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3
  110 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 260 2 1 55 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 260 (accept_3_2 1
  110 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 260 (allA_of_3_0 109 109 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 260
  (allA_succ_of_accept 107 108 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 107 108 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 260 2 53 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 108 260
  (Polychromatic418967fa.accept_16_9_12_4_1_3255 105 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 108 260 4 26 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 108 260 (accept_3_2 103 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 260 2 51 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 101 108 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 108 260 4 25 27 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 108 260
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 99 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 108 260 2 49 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 108 260 (accept_3_2 97 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 260 4 24 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 108 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 108 260 2 47 54 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 108 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 108 260 4 23 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 108 260 (accept_3_2 91 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 260 2 45 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 108 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 260 4 22 27 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 108 260
  (Polychromatic418967fa.accept_16_7_12_4_1_1347 87 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 108 260 2 43 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 108 260 (accept_3_2 85 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 260 4 21 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 260 (Polychromatic418967fa.accept_15_8_3_5_1_608 83 108 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 260 2 41 54 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 108 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 108 260 4 20 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 108 260 (accept_3_2 79 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 260 2 39 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 260 (Polychromatic418967fa.accept_15_2_3_5_1_2991 77 108 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 260 4 19 27 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 108 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 108 260 2 37 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 108 260 (accept_3_2 73 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 260 4 18 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 260 (Polychromatic418967fa.accept_11_5_9_7_1_411 71 108 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 260 2 35 54 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 108 260
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 69 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 108 260 4 17 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 108 260 (accept_3_2 67 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 260 2 33 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 108 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 260 4 16 27 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 108 260
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 63 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 108 260 2 31 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 108 260 (accept_3_2 61 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 260 4 15 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 260 (Polychromatic418967fa.accept_16_11_12_4_1_3195 59 108 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 260 2 29 54 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 260
  (Polychromatic418967fa.accept_11_2_9_7_1_124 57 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 260 4 14 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 260 (accept_3_2 55 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 260 2 27 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 108 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 260 4 13 27 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 260 2 25 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 260 (accept_3_2 49 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 260 4 12 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 108 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 260 2 23 54 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 260
  (Polychromatic418967fa.accept_16_13_12_4_1_4323 45 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 108 260 4 11 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 108 260 (accept_3_2 43 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 260 2 21 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 260 (Polychromatic418967fa.accept_16_9_12_4_1_3255 41 108 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 260 4 10 27 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 260 2 19 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 260 (accept_3_2 37 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 260 4 9 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 108 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 260 2 17 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 33
  108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 260 4 8 27 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 260 (accept_3_2 31
  108 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 260 2 15 54 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 260
  (Polychromatic418967fa.accept_16_13_12_4_1_4323 29 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 108 260 4 7 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 108 260 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 108 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 260 2 13 54 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 260 (accept_3_2 25 108 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 260 4 6 27 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 260 2 11 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 108 260 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 108 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 260 4 5 27 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 260 (accept_3_2 19 108 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 260 2 9 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 260 (Polychromatic418967fa.accept_15_2_3_5_1_2991
  17 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 260 4 4 27 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 260
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 108 260 2 7 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 260 (accept_3_2 13 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 260 4 3 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 108 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 260 2 5 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9
  108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 260 4 2 27 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 260 (accept_3_2 7
  108 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 260 2 3 54 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 108 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 260 4 1 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 108 260 (Polychromatic418967fa.accept_16_3_12_4_1_170 3 108 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 260 2 1 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 260 (accept_3_2 1 108 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 260 (allA_succ_of_accept 106 107 260 (accept_3_2 106 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 107 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 104 107
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 260 (accept_3_2 103 107
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 260
  (Polychromatic418967fa.accept_15_12_2_5_1_3939 102 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 107 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 260 (accept_3_2 100 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 107 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 98 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 260 (accept_3_2 97 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 260 (Polychromatic418967fa.accept_19_1_12_13_1_6279 96 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 95 107 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 260 (accept_3_2 94 107 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 260
  (Polychromatic418967fa.accept_11_4_8_7_1_819 92 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 260 (accept_3_2 91 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 260 (Polychromatic418967fa.accept_15_14_2_5_1_1272 89 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 260 (accept_3_2 88 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 107 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 86 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 260 (accept_3_2 85 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 260 (Polychromatic418967fa.accept_24_12_11_20_1_15854 84 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 83 107 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 260 (accept_3_2 82 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 107 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 260 (accept_3_2 79 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 260 (Polychromatic418967fa.accept_15_3_2_5_1_2980 78 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 260 (Polychromatic418967fa.accept_18_5_17_8_1_2984 77 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 260 (accept_3_2 76 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 74 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 260 (accept_3_2 73 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 260 (Polychromatic418967fa.accept_15_12_2_5_1_3939 72 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 107 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 260 (accept_3_2 70 107 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 260
  (Polychromatic418967fa.accept_19_11_12_13_1_4844 68 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 107 260 (accept_3_2 67 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 107 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 107 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 260 (Polychromatic418967fa.accept_22_21_19_18_1_12827 65
  107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 260 (accept_3_2 64
  107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 107 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 107 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 260 (accept_3_2 61 107 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 107 260 (Polychromatic418967fa.accept_16_12_11_4_1_1359 60 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 260 (accept_3_2 58 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 260 (Polychromatic418967fa.accept_15_11_2_5_1_2076 56 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 260 (accept_3_2 55 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 260 (Polychromatic418967fa.accept_16_6_11_4_1_635 54 107
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 260
  (Polychromatic418967fa.accept_22_9_19_18_1_15853 53 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 107 260 (accept_3_2 52 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 107
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 260 (accept_3_2 49 107
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 107 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 107 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 260 (accept_3_2 46 107 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 107 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 260
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 44 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 260 (accept_3_2 43 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 260 (Polychromatic418967fa.accept_15_12_2_5_1_3939 42 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 107 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 260 (accept_3_2 40 107 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 260 (accept_3_2 37 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 260 (Polychromatic418967fa.accept_21_15_2_8_1_14291 36 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 260 (Polychromatic418967fa.accept_19_16_12_13_1_4843 35 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 260 (accept_3_2 34 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 260
  (Polychromatic418967fa.accept_23_9_15_7_1_15842 32 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 107 260 (accept_3_2 31 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 107 260 (Polychromatic418967fa.accept_19_11_12_13_1_4844 30 107 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 260 (Polychromatic418967fa.accept_14_1_9_8_1_2863
  29 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 260 (accept_3_2 28
  107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 107 260 (Polychromatic418967fa.accept_11_4_8_7_1_819 26 107 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 260 (accept_3_2 25 107 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 107 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 107 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 260 (Polychromatic418967fa.accept_8_7_3_4_1_404
  23 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 260 (accept_3_2 22
  107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 107 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 107 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 260 (accept_3_2 19 107 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 107 260 (Polychromatic418967fa.accept_15_3_2_5_1_2980 18 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 260 (accept_3_2 16 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 260 (accept_3_2 13 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 260 (Polychromatic418967fa.accept_15_12_2_5_1_3939 12 107
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 260
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 260 (accept_3_2 10 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 260 (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 260 (accept_3_2 7 107 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 107 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 260
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 5 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 260 (accept_3_2 4 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 107 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 260 (accept_3_2 1 107 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 260 (allA_of_3_0 106 106 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 260
  (allA_succ_of_accept 104 105 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 104 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 260 (accept_3_2 103 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 105 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 105 260 5 20 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 105 260 (Polychromatic418967fa.accept_14_1_7_8_1_2063 99 105 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 260
  (Polychromatic418967fa.accept_19_3_10_13_1_3482 98 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 105 260 (accept_3_2 97 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 105 260 (Polychromatic418967fa.accept_19_1_10_13_1_4880 96 105 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 105 260 5 19 21 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 105 260 (accept_3_2 94 105 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 105 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 93 105 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 92 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 105 260 (accept_3_2 91 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90
  105 260 5 18 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 105 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 260 (accept_3_2 88 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 105 260 (Polychromatic418967fa.accept_17_2_3_5_1_763 87 105 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 86 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 105 260 5 17 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 84 105 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 105 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 260 (accept_3_2 82
  105 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 105 260
  (Polychromatic418967fa.accept_19_5_10_13_1_4883 81 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 105 260 5 16 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 105 260 (accept_3_2 79 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 105 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 78 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 105 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 260 (accept_3_2 76 105 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 105 260 5 15 21 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 105 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 260 (accept_3_2 73 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 105 260 (Polychromatic418967fa.accept_16_8_9_4_1_630 72 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 105 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 105 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 260 5 14 21 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 105 260
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 105 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 260 (accept_3_2 67 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 105 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 105 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 105 260 5 13 21 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 105 260 (accept_3_2 64 105 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 105 260 (Polychromatic418967fa.accept_19_6_10_13_1_4839 63 105
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 260
  (Polychromatic418967fa.accept_14_6_7_8_1_624 62 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 260 (accept_3_2 61 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  105 260 5 12 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 105 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 260 (accept_3_2 58 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 105 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 260 (Polychromatic418967fa.accept_9_2_6_8_1_321
  56 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 105 260 5 11 21 52
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 105 260
  (Polychromatic418967fa.accept_12_6_9_8_1_165 54 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 260 (accept_3_2 52 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 260 (Polychromatic418967fa.accept_22_7_17_18_1_15852 51 105 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 105 260 5 10 21 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 105 260 (accept_3_2 49 105 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 260 (Polychromatic418967fa.accept_9_3_6_8_1_308
  48 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 260 (accept_3_2 46 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  105 260 5 9 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 105 260 (Polychromatic418967fa.accept_16_12_9_4_1_4345 44 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 105 260 (accept_3_2 43 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 105 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 260 5 8 21 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 105 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 105 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 260 (accept_3_2 37 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 105 260 (Polychromatic418967fa.accept_17_2_3_5_1_763 36 105 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 260 5 7 21 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 260 (accept_3_2 34 105 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 260
  (Polychromatic418967fa.accept_22_11_17_18_1_15851 33 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 105 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 260 (accept_3_2 31 105 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 260 5 6 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 260 (accept_3_2 28 105 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 260 (Polychromatic418967fa.accept_14_13_7_8_1_677
  27 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 260
  (Polychromatic418967fa.accept_22_4_17_18_1_12777 26 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 105 260 5 5 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 105 260 (Polychromatic418967fa.accept_16_8_9_4_1_630 24 105 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 260 (accept_3_2 22 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 105 260 5 4 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 105 260 (accept_3_2 19 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 260 (accept_3_2 16 105 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 260 5 3 21 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 260 (accept_3_2 13 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 260 5 2 21 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 105 260
  (Polychromatic418967fa.accept_19_9_10_13_1_2291 9 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 260 (Polychromatic418967fa.accept_16_8_9_4_1_630 8 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 260 (accept_3_2 7 105 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 105 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 260 5 1 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 260 (accept_3_2 4 105 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 105 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 260 (accept_3_2 1 105 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 260 (allA_succ_of_accept 103 104 260 (accept_3_2 103 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 260 2 51 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 104 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 260 4 25 26 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 260
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 99 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 260 2 49 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 260 (accept_3_2 97 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 260 4 24 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 260 (Polychromatic418967fa.accept_16_15_8_4_1_1355 95 104 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 260 2 47 52 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 93 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 260 4 23 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 91 104 260 13 7 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 90 104 260 2 45 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 104 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 104 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 260 4 22 26 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 87 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 260 2 43 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 260 (accept_3_2 85 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 260 4 21 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 104 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 260 2 41 52 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 260
  (Polychromatic418967fa.accept_15_6_14_5_1_2976 81 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 260 4 20 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 260 (accept_3_2 79 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 260 26 3 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 104 260 (Polychromatic418967fa.accept_14_7_6_8_1_2856 77 104 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 260 4 19 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 75
  104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 104 260 2 37 52 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 104 260 (accept_3_2 73
  104 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 104 260 4 18 26 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 104 260
  (Polychromatic418967fa.accept_16_7_8_4_1_689 71 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 104 260 2 35 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 104 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 104 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 104 260 4 17 26 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 104 260 (accept_3_2 67 104 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 104 260 2 33 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 104 260 13 5 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 104 260 4 16 26 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 260
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 63 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 260 2 31 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 260 (accept_3_2 61 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 260 4 15 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 260 (Polychromatic418967fa.accept_16_11_8_4_1_2234 59 104 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 260 2 29 52 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 260 4 14 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 260 (accept_3_2 55 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 260 2 27 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 53 104 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 260 52 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 104 260 2 25 52 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 104 260 (accept_3_2 49
  104 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 104 260 4 12 26 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 104 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 104 260 2 23 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 104 260 (Polychromatic418967fa.accept_16_13_8_4_1_3250 45 104 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 104 260 4 11 26 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 104 260 (accept_3_2 43 104 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 104 260 2 21 52 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 104 260
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 41 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 104 260 4 10 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 104 260 13 3 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 104 260 2 19 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 104 260 (accept_3_2 37 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 260 4 9 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 104 260 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 104 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 260 2 17 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 33
  104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 260 4 8 26 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 260 (accept_3_2 31
  104 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 260 2 15 52 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 104 260 4 7 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 104 260 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 104 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 260 26 1 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 260 (accept_3_2 25 104 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 104 260 4 6 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 104 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 104 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 260 2 11 52 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 260 4 5 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 104 260 (accept_3_2 19 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  104 260 2 9 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 260 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 104 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 260 4 4 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 260 2 7 52 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 104 260 13 1 8 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 104 260 4 3 26 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 260 2 5 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 104 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 104 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 260 4 2 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 260 (accept_3_2 7 104 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104 260 2 3 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 104 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 104 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 260 4 1 26 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 104 260 2 1 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 104 260 (accept_3_2 1 104 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 260 (allA_of_3_0 103 103 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 260 (allA_succ_of_accept 101
  102 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 102 260 2 50 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 102 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 102 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 260 2 49 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 260 (accept_3_2 97 102 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 260 2 48 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 95 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 260 2 47 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 93 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 260 2 46 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 260 (accept_3_2 91 102 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 102 260 2 45 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 89
  102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 260 2 44 51 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 102 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 87 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 102 260 2 43 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 102 260 (accept_3_2 85 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 260 2 42 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 260 2 41 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 102 260
  (Polychromatic418967fa.accept_11_4_3_7_1_828 81 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 102 260 2 40 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 102 260 (accept_3_2 79 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 260 2 39 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 260 2 38 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 102 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 102 260 2 37 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 260 (accept_3_2 73 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 260 2 36 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 260 (Polychromatic418967fa.accept_28_15_18_8_1_15850 71 102 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 260 2 35 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 69 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 260 2 34 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 260 (accept_3_2 67 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 260 2 33 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 260 2 32 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 260 2 31 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 260 (accept_3_2 61 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 260 2 30 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 260 2 29 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 260 2 28 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 260 (accept_3_2 55 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 260 2 27 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 260 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 102 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 260 2 26 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 260 2 25 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 260 (accept_3_2 49 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 260 2 24 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 260 2 23 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 260 2 22 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 260 (accept_3_2 43 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 260 2 21 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 260 2 20 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 260 2 19 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 260 (accept_3_2 37 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 260 2 18 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 260 (Polychromatic418967fa.accept_16_3_6_4_1_679 35 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 260 2 17 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 260 2 16 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 260 (accept_3_2 31 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 260 2 15 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 260 2 14 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 260 2 13 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 260 (accept_3_2 25 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 260 2 12 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 260 2 11 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 260
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 260 2 10 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 260 (accept_3_2 19 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 260 2 9 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 260 2 8 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 102 260 2 7 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 102 260 (accept_3_2 13 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 260 2 6 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 260 2 5 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 260 2 4 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 260 (accept_3_2 7 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102
  260 2 3 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 102 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 260 2 2 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 102 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 102 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 260 2 1 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 260 (accept_3_2 1 102 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 260 (allA_succ_of_accept 100 101 260 (accept_3_2 100 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 101 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 98 101
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 260 (accept_3_2 97 101
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 96 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 101 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 260 (accept_3_2 94 101 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 260
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 92 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 101 260 (accept_3_2 91 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 101 260 (Polychromatic418967fa.accept_22_2_13_18_1_6373 90 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 101 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 260 (accept_3_2 88 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 86 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 260 (accept_3_2 85 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 83 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 260 (accept_3_2 82 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 260
  (Polychromatic418967fa.accept_19_4_6_13_1_6335 80 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 260 (accept_3_2 79 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 260 (accept_3_2 76 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 260 (accept_3_2 73 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 260 (Polychromatic418967fa.accept_22_5_13_18_1_12746 71 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 260 (accept_3_2 70 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 68 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 260 (accept_3_2 67 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 260 (accept_3_2 64 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 260 (accept_3_2 61 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 260 (accept_3_2 58 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 260
  (Polychromatic418967fa.accept_16_8_5_4_1_674 56 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 260 (accept_3_2 55 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 260 (accept_3_2 52 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 260 (accept_3_2 49 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 260 (accept_3_2 46 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 260 (accept_3_2 43 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 260 (accept_3_2 40 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 260 (accept_3_2 37 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 260 (Polychromatic418967fa.accept_17_1_16_5_1_3670 35 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 260 (accept_3_2 34 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 260 (accept_3_2 31 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 260 (Polychromatic418967fa.accept_19_10_6_13_1_4830 29 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 260 (accept_3_2 28 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 260 (accept_3_2 25 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 260 (accept_3_2 22 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 260
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 260 (accept_3_2 19 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 260 (accept_3_2 16 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 260 (accept_3_2 13 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 260 (accept_3_2 10 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 260
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 260 (accept_3_2 7 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 260 (accept_3_2 4 101 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 260 (accept_3_2 1 101 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 260 (allA_of_3_0 100 100 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 260 (allA_succ_of_accept 98 99
  260 (Polychromatic418967fa.accept_19_3_4_13_1_4864 98 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 99 260 (accept_3_2 97 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 99 260 (Polychromatic418967fa.accept_18_6_9_8_1_6812 96 99 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 99 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 260 (accept_3_2 94 99 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 260 (Polychromatic418967fa.accept_14_9_1_8_1_2849
  93 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 260
  (Polychromatic418967fa.accept_16_12_3_4_1_4317 92 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 260 (accept_3_2 91 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 260 (accept_3_2 88 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 99 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 260
  (Polychromatic418967fa.accept_14_2_1_8_1_650 86 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 260 (accept_3_2 85 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 260 (Polychromatic418967fa.accept_19_8_4_13_1_4912 84 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 260 (accept_3_2 82 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 260 (Polychromatic418967fa.accept_16_1_3_4_1_665 81 99 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 260
  (Polychromatic418967fa.accept_21_17_15_8_1_6799 80 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 260 (accept_3_2 79 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 260 (accept_3_2 76 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 260 (Polychromatic418967fa.accept_18_3_9_8_1_2977 75 99 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 260
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 74 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 260 (accept_3_2 73 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 260 (Polychromatic418967fa.accept_14_2_1_8_1_650 72 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 260 (accept_3_2 70 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 260 (Polychromatic418967fa.accept_21_6_15_8_1_9895 69 99 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 260
  (Polychromatic418967fa.accept_21_5_15_8_1_9935 68 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 260 (accept_3_2 67 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 260 (accept_3_2 64 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 99 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 260
  (Polychromatic418967fa.accept_27_8_18_17_1_15849 62 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 99 260 (accept_3_2 61 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 99 260 (Polychromatic418967fa.accept_16_12_3_4_1_4317 60 99 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 260 (accept_3_2 58 99 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973
  57 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 260
  (Polychromatic418967fa.accept_15_11_9_5_1_2974 56 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 260 (accept_3_2 55 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 260 (accept_3_2 52 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 260 (Polychromatic418967fa.accept_14_9_1_8_1_2849 51 99 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 260
  (Polychromatic418967fa.accept_22_6_11_18_1_11255 50 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 99 260 (accept_3_2 49 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 99 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 48 99 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 260 (accept_3_2 46 99 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 260 (Polychromatic418967fa.accept_19_7_4_13_1_6319
  45 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 260
  (Polychromatic418967fa.accept_14_2_1_8_1_650 44 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 260 (accept_3_2 43 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 260 (accept_3_2 40 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 99 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 260
  (Polychromatic418967fa.accept_16_6_3_4_1_6624 38 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 260 (accept_3_2 37 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 260 (Polychromatic418967fa.accept_17_2_14_5_1_2575 36 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 260 (accept_3_2 34 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 33 99 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 260
  (Polychromatic418967fa.accept_22_10_11_18_1_14206 32 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 99 260 (accept_3_2 31 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 99 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 99 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 260 (accept_3_2 28 99 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973
  27 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 260
  (Polychromatic418967fa.accept_15_11_9_5_1_2974 26 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 260 (accept_3_2 25 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 260 (Polychromatic418967fa.accept_16_8_3_4_1_3233 24 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 260 (accept_3_2 22 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 260 (Polychromatic418967fa.accept_14_7_1_8_1_2873 21 99 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 260
  (Polychromatic418967fa.accept_25_20_24_10_1_8806 20 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 99 260 (accept_3_2 19 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 99 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 99 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 260 (accept_3_2 16 99 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 15
  99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 260
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 260 (accept_3_2 13 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 260 (accept_3_2 10 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 260 (Polychromatic418967fa.accept_14_9_1_8_1_2849 9 99 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 260
  (Polychromatic418967fa.accept_16_8_3_4_1_3233 8 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 260 (accept_3_2 7 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  260 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 260 (accept_3_2 4 99 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 99 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 260 (Polychromatic418967fa.accept_14_2_1_8_1_650 2
  99 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 260 (accept_3_2 1 99 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  260 (allA_succ_of_accept 97 98 260 (accept_3_2 97 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 260 2 48 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 98 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 260 2 47 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105
  93 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 260 2 46 49 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 98 260
  (accept_3_2 91 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 98 260 2 45 49 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 89 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 260 2 44 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 260 (Polychromatic418967fa.accept_15_12_8_5_1_5048 87 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 260 2 43 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 260 (accept_3_2 85 98 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 260 2 42 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 260 (Polychromatic418967fa.accept_12_11_2_8_1_511
  83 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 260 2 41 49 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 260
  (Polychromatic418967fa.accept_29_23_11_28_1_13860 81 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 98 260 2 40 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 98 260 (accept_3_2 79 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 260 2 39 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 98 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 260 2 38 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 260
  (Polychromatic418967fa.accept_21_12_14_8_1_5258 75 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 260 2 37 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 98 260 (accept_3_2 73 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 260 2 36 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 98 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 260 2 35 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 260
  (Polychromatic418967fa.accept_11_3_10_7_1_129 69 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 98 260 2 34 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 98 260 (accept_3_2 67 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 98 260 2 33 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 98 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 260 2 32 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 260
  (Polychromatic418967fa.accept_15_3_8_5_1_2105 63 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 98 260 2 31 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 98 260 (accept_3_2 61 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 260 2 30 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 98 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 260 2 29 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 260
  (Polychromatic418967fa.accept_15_12_8_5_1_5048 57 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 260 2 28 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 98 260 (accept_3_2 55 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 98 260 2 27 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 260 2 26 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 260
  (Polychromatic418967fa.accept_23_5_6_7_1_15848 51 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 260 2 25 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 98 260 (accept_3_2 49 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 98 260 2 24 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 98 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 47 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 260 2 23 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 260
  (Polychromatic418967fa.accept_19_7_3_13_1_3492 45 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 260 2 22 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 98 260 (accept_3_2 43 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 260 2 21 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 260 2 20 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 260
  (Polychromatic418967fa.accept_22_17_10_18_1_15847 39 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 98 260 2 19 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 98 260 (accept_3_2 37 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 98 260 2 18 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 98 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 260 2 17 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 260
  (Polychromatic418967fa.accept_15_3_8_5_1_2105 33 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 260 2 16 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 260 (accept_3_2 31 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 260 2 15 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 260 2 14 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 260
  (Polychromatic418967fa.accept_15_12_8_5_1_5048 27 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 260 2 13 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 98 260 (accept_3_2 25 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 260 2 12 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 260 2 11 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 260
  (Polychromatic418967fa.accept_22_21_10_18_1_11241 21 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 98 260 2 10 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 98 260 (accept_3_2 19 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 260 2 9 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 260 2 8 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 260 (Polychromatic418967fa.accept_17_15_13_5_1_9877
  15 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 260 2 7 49 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 260 (accept_3_2 13
  98 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 260 2 6 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 98 260 2 5 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 98 260 (Polychromatic418967fa.accept_17_9_13_5_1_3512 9 98 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 260 2 4 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 260 (accept_3_2 7 98 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 98 260 2 3 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 98 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 98 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 260 2 2 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 3
  98 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 260 2 1 49 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 260 (accept_3_2 1 98
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  260 (allA_of_3_0 97 97 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 260 (allA_succ_of_accept 95 96 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 95 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 96 260 2 47 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 96 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 96 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 96 260 4 23 24 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 260 (accept_3_2 91 96 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 260 2 45 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 260 (Polychromatic418967fa.accept_15_14_6_5_1_7215
  89 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 260 4 22 24 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 260 2 43 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 260 (accept_3_2 85 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 260 4 21 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 96 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 260 2 41 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 81
  96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 260 4 20 24 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 260 (accept_3_2 79
  96 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 260 2 39 48 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 260 4 19 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 96 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 96 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 260 2 37 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 260 (accept_3_2 73 96 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 260 4 18 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 260 (Polychromatic418967fa.accept_15_11_6_5_1_1295 71 96 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 260 2 35 48 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 260 4 17 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 260 (accept_3_2 67 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96
  260 2 33 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  65 96 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 96 260 4 16 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 96 260 (Polychromatic418967fa.accept_15_3_6_5_1_2079 63 96 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 260 2 31 48 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 260 (accept_3_2 61 96 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 260 4 15 24 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 96 260 2 29 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 96 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 96 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 260 4 14 24 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 260 (accept_3_2 55 96 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 260 2 27 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 53
  96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 260 4 13 24 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 260
  (Polychromatic418967fa.accept_21_9_12_8_1_5255 51 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 96 260 2 25 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 96 260 (accept_3_2 49 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 260 4 12 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 260 2 23 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 45
  96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 260 4 11 24 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 260 (accept_3_2 43
  96 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 260 2 21 48 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 260 4 10 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 96 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 96 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 260 2 19 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 260 (accept_3_2 37 96 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 260 4 9 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 96 260 (Polychromatic418967fa.accept_19_16_1_13_1_4860 35 96 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 260 2 17 48 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 260
  (Polychromatic418967fa.accept_15_3_6_5_1_2079 33 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 260 4 8 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 260 (accept_3_2 31 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96
  260 2 15 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 96 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 96 260 4 7 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 96 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 260 2 13 48 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 260 (accept_3_2 25 96 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 260 4 6 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 260 2 11 48 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 260 4 5 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 260 (accept_3_2 19 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96
  260 2 9 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  96 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 260 4 4 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 260 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 96 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 260 2 7 48 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 260 (accept_3_2 13 96 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 260 4 3 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 96 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 260 2 5 48 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 260
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 9 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 260 4 2 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 260 (accept_3_2 7 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 260
  2 3 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96
  260 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 260 4 1 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 260 2 1 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 260 (accept_3_2 1 96 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 260
  (allA_succ_of_accept 94 95 260 (accept_3_2 94 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 95 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 260 (accept_3_2 91 95 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 90 95 260 5 18 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 95 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 95 260 (accept_3_2 88 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87
  95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 86 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 95 260 5 17 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 95 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 83 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 260 (accept_3_2 82 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81
  95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 95 260 5 16 19 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 95 260 (accept_3_2 79
  95 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 78 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 95 260 (Polychromatic418967fa.accept_21_14_11_8_1_5272 77 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 260 (accept_3_2 76 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 95 260 5 15 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 95 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 95 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 260 (accept_3_2 73 95 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 260 (Polychromatic418967fa.accept_16_8_15_4_1_5402 72 95
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 260
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 71 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 95 260 5 14 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 260 (accept_3_2 67 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 66
  95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 95 260 5 13 19 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 95 260 (accept_3_2 64
  95 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 95 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 260 (accept_3_2 61 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 95 260 5 12 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 95 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 95 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 260 (accept_3_2 58 95 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 95 260 5 11 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 95 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 260 (Polychromatic418967fa.accept_16_5_15_4_1_9099 53 95
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 260 (accept_3_2 52 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51
  95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 260 5 10 19 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 260 (accept_3_2 49
  95 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 95 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 260 (accept_3_2 46 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 95 260 5 9 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 95 260 (Polychromatic418967fa.accept_16_12_15_4_1_5422 44 95 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 260 (accept_3_2 43 95 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 260
  (Polychromatic418967fa.accept_21_20_11_8_1_9906 41 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 95 260 5 8 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 260 (accept_3_2 37 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 260
  (Polychromatic418967fa.accept_22_14_7_18_1_15836 36 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 95 260 5 7 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 95 260 (accept_3_2 34 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 95
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 260 (accept_3_2 31 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 95 260 5 6 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 95 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 29
  95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 260 (accept_3_2 28 95
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12
  27 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 95 260 5 5 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 95 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 260 (Polychromatic418967fa.accept_22_1_7_18_1_12741 23 95
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 260 (accept_3_2 22 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 260 5 4 19 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 260 (accept_3_2 19
  95 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 260
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 260 (accept_3_2 16 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 95 260 5 3 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 95 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 95 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 260 (accept_3_2 13 95 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 95 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 95 260 5 2 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 260 (Polychromatic418967fa.accept_16_8_15_4_1_5402 8 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 260 (accept_3_2 7 95 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 6
  95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 260 5 1 19 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 260 (accept_3_2 4 95
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 260 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 260 (accept_3_2 1 95 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 260
  (allA_of_3_0 94 94 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 260 (allA_succ_of_accept 92 93 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 260 (accept_3_2 91 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 260 (accept_3_2 88 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 260 (accept_3_2 85 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 84 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 260 (accept_3_2 82 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 260 (accept_3_2 79 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 260 (accept_3_2 76 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 75 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 260 (accept_3_2 73 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 260 (Polychromatic418967fa.accept_16_8_13_4_1_3258 72 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 260 (accept_3_2 70 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 260 (accept_3_2 67 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 260 (accept_3_2 64 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 260 (Polychromatic418967fa.accept_17_12_8_5_1_6018 63 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 260 (accept_3_2 61 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 260 (accept_3_2 58 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 260 (accept_3_2 55 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 260 (accept_3_2 52 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 260 (accept_3_2 49 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 260 (accept_3_2 46 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 260
  (Polychromatic418967fa.accept_16_12_13_4_1_3198 44 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 260 (accept_3_2 43 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 260 (accept_3_2 40 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 260 (accept_3_2 37 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 260 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 260 (accept_3_2 34 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 260 (accept_3_2 31 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 260 (accept_3_2 28 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 260
  (Polychromatic418967fa.accept_19_7_17_13_1_9166 26 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 260 (accept_3_2 25 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 260 (accept_3_2 22 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 260 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 260 (accept_3_2 19 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 260 (accept_3_2 16 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 260 (accept_3_2 13 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 260 (Polychromatic418967fa.accept_16_12_13_4_1_3198 12 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 260 (accept_3_2 10 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 260
  (Polychromatic418967fa.accept_15_8_3_5_1_608 8 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 260 (accept_3_2 7 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  260 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 260 (accept_3_2 4 93 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 93 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  93 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 260 (accept_3_2 1 93 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 260
  (allA_succ_of_accept 91 92 260 (accept_3_2 91 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  260 2 45 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 260 (Polychromatic418967fa.accept_15_14_2_5_1_1272 89 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 260 4 22 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 92 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 260 2 43 46 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 260 (accept_3_2 85 92 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 260 4 21 23 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 260
  (Polychromatic418967fa.accept_16_3_12_4_1_170 83 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 260 2 41 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 260 (Polychromatic418967fa.accept_16_1_12_4_1_695 81 92 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 260 4 20 23 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 260 (accept_3_2 79 92 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 260 2 39 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 77
  92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 260 4 19 23 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 260 2 37 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 92 260 (accept_3_2 73 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 260 4 18 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 92 260 (Polychromatic418967fa.accept_15_11_2_5_1_2076 71 92 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 260 2 35 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 69
  92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 260 4 17 23 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 260 (accept_3_2 67
  92 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 260 2 33 46 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 260
  (Polychromatic418967fa.accept_16_1_12_4_1_695 65 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 260 4 16 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 92 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 260 2 31 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 260 (accept_3_2 61 92 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 260 4 15 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 92 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 260 2 29 46 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 260 4 14 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 260 (accept_3_2 55 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  260 2 27 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 92 260 (Polychromatic418967fa.accept_16_5_12_4_1_4325 53 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 260 4 13 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 92 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 260 2 25 46 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 260 (accept_3_2 49 92 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 260 4 12 23 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 260
  (Polychromatic418967fa.accept_11_3_4_7_1_114 47 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 260 2 23 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 92 260 (Polychromatic418967fa.accept_16_13_12_4_1_4323 45 92 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 260 4 11 23 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 260 (accept_3_2 43 92 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 260 2 21 46 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 92 260 4 10 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 92 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 92 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 92 260 2 19 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 92 260 (accept_3_2 37 92 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92 260 4 9 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 92 260 (Polychromatic418967fa.accept_16_3_12_4_1_170 35 92 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 260 2 17 46 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 260 4 8 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 92 260 (accept_3_2 31 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92
  260 2 15 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 92 260 (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 92 260 4 7 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 92 260 (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 92 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 260 2 13 46 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 260 (accept_3_2 25 92 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 260 4 6 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 92 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 260 2 11 46 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 260 4 5 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 260 (accept_3_2 19 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  260 2 9 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 260 (Polychromatic418967fa.accept_16_1_12_4_1_695 17 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 260 4 4 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 92 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 260 2 7 46 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 260 (accept_3_2 13 92 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 260 4 3 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 260 (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 92 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 260 2 5 46 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 260
  (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 260 4 2 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 260 (accept_3_2 7 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 260
  2 3 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  260 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 92 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 260 4 1 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 92 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 260 2 1 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 260 (accept_3_2 1 92 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 260
  (allA_of_3_0 91 91 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 260 (allA_succ_of_accept 89 90 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 89 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 90 260 2 44 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 90 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 87 90 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 260 2 43 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 90 260 5 17 18 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 90 260 2 42 45 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 260
  (Polychromatic418967fa.accept_23_14_21_7_1_15846 83 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 90 260 2 41 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 90 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 81 90 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 90 260 10 8 9 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 260 (accept_3_2 79 90 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 260 2 39 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 260 (Polychromatic418967fa.accept_14_7_6_8_1_2856
  77 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 260 2 38 45 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 90 260 5 15 18 52
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 90 260 2 37 45
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 260
  (accept_3_2 73 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 260 2 36 45 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 260
  (Polychromatic418967fa.accept_22_5_2_18_1_4720 71 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 90 260 10 7 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 90 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 69 90 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 260 2 34 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 260 (accept_3_2 67 90 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 260 2 33 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 90 260 5 13 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 90 260 2 32 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 63
  90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 260 2 31 45 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 260 (accept_3_2 61
  90 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 260 10 6 9 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 260
  (Polychromatic418967fa.accept_25_9_15_10_1_8748 59 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 90 260 2 29 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 90 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 57 90 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 260 2 28 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 90 260 5 11 18 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 90 260 2 27 45 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 260
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 53 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 90 260 2 26 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 90 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 90 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 260 10 5 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 260 (accept_3_2 49 90 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 260 2 24 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 90 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 260 2 23 45 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 260 5 9 18 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 260 2 22 45 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 260
  (accept_3_2 43 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 260 2 21 45 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 260
  (Polychromatic418967fa.accept_25_16_15_10_1_15845 41 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 90 260 10 4 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 90 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 39 90 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 260 2 19 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 260 (accept_3_2 37 90 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 260 2 18 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 260 5 7 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 90 260 2 17 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 260 2 16 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 90 260 (accept_3_2 31 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 260 10 3 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 90 260 (Polychromatic418967fa.accept_22_7_2_18_1_12758 29 90 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 260 2 14 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 27
  90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 260 2 13 45 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 90 260 5 5 18 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 260 2 12 45 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 260 2 11 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 90 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 260 10 2 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 260 (accept_3_2 19 90 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 260 2 9 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 260 (Polychromatic418967fa.accept_28_17_6_8_1_15844 17 90
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 260 2 8 45 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 260 5 3 18 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 260 2 7 45 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 260 (accept_3_2 13
  90 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 260 2 6 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 260
  (Polychromatic418967fa.accept_25_11_15_10_1_12386 11 90 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 260 10 1 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 90 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 260 2 4 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 260 (accept_3_2 7 90 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 260 2 3 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 260 5 1 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 4 90 260 2 2 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 90 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 90 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 260 2 1 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 260 (accept_3_2 1 90 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 260
  (allA_succ_of_accept 88 89 260 (accept_3_2 88 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 86 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 260 (accept_3_2 85 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 260 (Polychromatic418967fa.accept_15_9_14_5_1_2086 84 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 83 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 260 (accept_3_2 82 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 80 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 260 (accept_3_2 79 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 260 (Polychromatic418967fa.accept_16_14_9_4_1_6693 78 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 260
  (Polychromatic418967fa.accept_8_5_1_4_1_628 77 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 260 (accept_3_2 76 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 260 (accept_3_2 73 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 72 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 260
  (Polychromatic418967fa.accept_22_5_1_18_1_15843 71 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 260 (accept_3_2 70 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 260 (Polychromatic418967fa.accept_15_8_14_5_1_2089 68 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 260 (accept_3_2 67 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 89 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 260
  (Polychromatic418967fa.accept_21_2_5_8_1_433 65 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 260 (accept_3_2 64 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 62 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 260 (accept_3_2 61 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 260 (accept_3_2 58 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 260 (Polychromatic418967fa.accept_16_8_9_4_1_630 56 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 260 (accept_3_2 55 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 260 (Polychromatic418967fa.accept_15_9_14_5_1_2086 54 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 260 (accept_3_2 52 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 50 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 260 (accept_3_2 49 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 260
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 260 (accept_3_2 46 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 260 (Polychromatic418967fa.accept_16_12_9_4_1_4345 44 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 260 (accept_3_2 43 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 260 (Polychromatic418967fa.accept_22_20_1_18_1_12757 42 89
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 260 (accept_3_2 40 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 260 (accept_3_2 37 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 260 (Polychromatic418967fa.accept_15_6_14_5_1_2976 36 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 260
  (Polychromatic418967fa.accept_17_1_4_5_1_3501 35 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 260 (accept_3_2 34 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 260 (accept_3_2 31 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 260 (Polychromatic418967fa.accept_16_14_9_4_1_6693 30 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 260
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 260 (accept_3_2 28 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 260 (accept_3_2 25 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 260
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 260 (accept_3_2 22 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 260 (accept_3_2 19 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 260 (accept_3_2 16 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 260 (accept_3_2 13 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 260 (Polychromatic418967fa.accept_16_12_9_4_1_4345 12 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 260 (accept_3_2 10 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 260 (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 260 (accept_3_2 7 89 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 89 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 260
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 260 (accept_3_2 4 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 89 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 260 (accept_3_2 1 89 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 260 (allA_of_3_0 88 88 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 260
  (allA_succ_of_accept 86 87 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 86 87 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 260 (accept_3_2 85 87 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 260 (accept_3_2 82 87
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 260 (Polychromatic418967fa.accept_7_4_3_1_1_87
  81 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 260
  (Polychromatic418967fa.accept_11_3_10_7_1_129 80 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 260 (accept_3_2 79 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 260 (accept_3_2 76 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 260 (accept_3_2 73 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 260 (accept_3_2 70 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 69 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 68 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 260 (accept_3_2 67 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 260 (accept_3_2 64 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 260 (Polychromatic418967fa.accept_19_6_11_13_1_4842 63 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 260
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 62 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 260 (accept_3_2 61 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 260 (accept_3_2 58 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 260 (accept_3_2 55 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 260 (accept_3_2 52 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 260 (accept_3_2 49 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 260 (accept_3_2 46 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 260 (Polychromatic418967fa.accept_16_13_7_4_1_3248 45 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 260 (accept_3_2 43 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 260 (accept_3_2 40 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 260 (accept_3_2 37 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 260 (accept_3_2 34 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 260 (accept_3_2 31 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 260 (accept_3_2 28 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 260 (accept_3_2 25 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 260 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 260 (accept_3_2 22 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 260 (accept_3_2 19 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 260 (accept_3_2 16 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 260 (Polychromatic418967fa.accept_21_15_3_8_1_6822 15 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 260 (accept_3_2 13 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 260 (accept_3_2 10 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 87 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 260
  (Polychromatic418967fa.accept_15_8_12_5_1_2987 8 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 260 (accept_3_2 7 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  260 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 87 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 260 (accept_3_2 4 87 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 87
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 260 (accept_3_2 1 87 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 260
  (allA_succ_of_accept 85 86 260 (accept_3_2 85 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  260 2 42 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 260 2 41 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 81 86 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 260 2 40 43 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 260 (accept_3_2 79 86 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 260 2 39 43 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 260 2 38 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 86 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 260 2 37 43 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 260 (accept_3_2 73 86 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 260 2 36 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 260 (Polychromatic418967fa.accept_11_5_9_7_1_411 71
  86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 260 2 35 43 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 260 2 34 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 86 260 (accept_3_2 67 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 86 260 2 33 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 86 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 86 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 260 2 32 43 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 260
  (Polychromatic418967fa.accept_19_6_10_13_1_4839 63 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 260 2 31 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 260 (accept_3_2 61 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 260 2 30 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 86 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 260 2 29 43 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 260 2 28 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 260 (accept_3_2 55 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 260 2 27 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 86 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 260 2 26 43 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 260 2 25 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 260 (accept_3_2 49 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 260 2 24 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 86 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 260 2 23 43 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 260 2 22 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 260 (accept_3_2 43 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 260 2 21 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 86 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 260 2 20 43 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 260 2 19 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 86 260 (accept_3_2 37 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 260 2 18 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 86 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 260 2 17 43 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 260 2 16 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 260 (accept_3_2 31 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 260 2 15 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 86 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 260 2 14 43 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 260 2 13 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 260 (accept_3_2 25 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 260 2 12 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 86 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 260 2 11 43 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 260 2 10 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 260 (accept_3_2 19 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 260 2 9 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 86 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 260 2 8 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 260 2 7 43 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 260 (accept_3_2 13
  86 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 260 2 6 43 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 86 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 260 2 5 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 260 (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 86 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 260 2 4 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 260 (accept_3_2 7 86 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 260 2 3 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 260 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 86 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 260 2 2 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 86
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 260 2 1 43 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 260 (accept_3_2 1 86
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 260
  (allA_of_3_0 85 85 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 260 (allA_succ_of_accept 83 84 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 260 2 41 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 84 260 (Polychromatic418967fa.accept_19_5_8_13_1_9161 81 84 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 260 4 20 21 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 260 (accept_3_2 79 84 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 260 2 39 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 77
  84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 260 4 19 21 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 260
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 75 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 260 2 37 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 260 (accept_3_2 73 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 260 4 18 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 260 (Polychromatic418967fa.accept_15_11_9_5_1_2974 71 84 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 260 2 35 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 69
  84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 260 4 17 21 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 260 (accept_3_2 67
  84 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 260 2 33 42 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 260 4 16 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 63 84 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 260 2 31 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 260 (accept_3_2 61 84 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 260 4 15 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 84 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 260 2 29 42 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 260
  (Polychromatic418967fa.accept_15_12_9_5_1_2973 57 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 260 4 14 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 260 (accept_3_2 55 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84
  260 2 27 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 84 260 (Polychromatic418967fa.accept_17_2_16_5_1_1584 53 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 84 260 4 13 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 84 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 84 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 260 2 25 42 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 260 (accept_3_2 49 84 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 260 4 12 21 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 260 2 23 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 84 260 (Polychromatic418967fa.accept_17_11_16_5_1_3612 45 84 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 260 4 11 21 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 260 (accept_3_2 43 84 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 260 2 21 42 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 260 4 10 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 84 260 (Polychromatic418967fa.accept_18_3_12_8_1_5415 39 84 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 260 2 19 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 260 (accept_3_2 37 84 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 260 4 9 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 84 260 (Polychromatic418967fa.accept_17_1_16_5_1_3670 35 84 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 260 2 17 42 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 260 4 8 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 260 (accept_3_2 31 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84
  260 2 15 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 84 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 84 260 4 7 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 84 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 84 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 260 2 13 42 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 260 (accept_3_2 25 84 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 260 4 6 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 260 2 11 42 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 260
  (Polychromatic418967fa.accept_17_4_16_5_1_8635 21 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 260 4 5 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 260 (accept_3_2 19 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  260 2 9 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 260 (Polychromatic418967fa.accept_23_17_15_7_1_11085 17 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 260 4 4 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 260 2 7 42 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 260 (accept_3_2 13 84 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 260 4 3 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 260 2 5 42 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 260
  (Polychromatic418967fa.accept_23_9_15_7_1_15842 9 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 260 4 2 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 260 (accept_3_2 7 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 260
  2 3 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  260 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 260 4 1 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 84 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 260 2 1 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 260 (accept_3_2 1 84 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 260 (allA_succ_of_accept 82 83 260 (accept_3_2 82 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 83 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 260 (Polychromatic418967fa.accept_19_4_7_13_1_3480 80 83
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 260 (accept_3_2 79 83 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 78
  83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 260 (accept_3_2 76 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 260 (accept_3_2 73 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 260
  (Polychromatic418967fa.accept_8_7_3_4_1_404 71 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 260 (accept_3_2 70 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 260 (accept_3_2 67 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 260 (accept_3_2 64 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 260 (accept_3_2 61 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 260 (accept_3_2 58 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 56 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 260 (accept_3_2 55 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 260
  (Polychromatic418967fa.accept_19_15_7_13_1_11844 53 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 83 260 (accept_3_2 52 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 83 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 260 (accept_3_2 49 83 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 48
  83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 260 (accept_3_2 46 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 260 (accept_3_2 43 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 260 (accept_3_2 40 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 260 (accept_3_2 37 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 260 (Polychromatic418967fa.accept_19_17_7_13_1_4833 36 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 260
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 35 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 260 (accept_3_2 34 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 260 (accept_3_2 31 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 260
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 260 (accept_3_2 28 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 260 (accept_3_2 25 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 260 (accept_3_2 22 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 260 (Polychromatic418967fa.accept_19_1_7_13_1_4813 20 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 260 (accept_3_2 19 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 83 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 260
  (Polychromatic418967fa.accept_16_1_3_4_1_665 17 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 260 (accept_3_2 16 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 260 (accept_3_2 13 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 260
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 260 (accept_3_2 10 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 260 (Polychromatic418967fa.accept_16_8_3_4_1_3233 8 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 260 (accept_3_2 7 83 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 260 (accept_3_2 4 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 83 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 260 (accept_3_2 1 83 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 260 (allA_of_3_0 82 82 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 260
  (allA_succ_of_accept 80 81 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 81 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 260 (accept_3_2 79 81 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 81 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 260 (accept_3_2 76 81
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 74 81 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 260 (accept_3_2 73 81 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 260 (Polychromatic418967fa.accept_15_12_6_5_1_1275 72 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 81 260 (accept_3_2 70 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  81 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 81 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 81 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 260 (accept_3_2 67 81 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 260 (accept_3_2 64 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  81 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 81 260 (Polychromatic418967fa.accept_16_14_1_4_1_5432 62 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 260 (accept_3_2 61 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 60 81
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 260 (accept_3_2 58 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 260 (Polychromatic418967fa.accept_15_12_6_5_1_1275 57 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 260 (Polychromatic418967fa.accept_15_11_6_5_1_1295 56 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 260 (accept_3_2 55 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 81 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 260 (accept_3_2 52 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 260 (Polychromatic418967fa.accept_16_3_1_4_1_5426 51 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 260 (Polychromatic418967fa.accept_19_12_5_13_1_14492 50 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 260 (accept_3_2 49 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 260 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 81 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 260 (accept_3_2 46 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 260 (Polychromatic418967fa.accept_15_14_6_5_1_7215 44 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 260 (accept_3_2 43 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 81 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 260 (accept_3_2 40 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 260 (Polychromatic418967fa.accept_18_3_9_8_1_2977 39 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 81 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 260 (accept_3_2 37 81 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 260 (accept_3_2 34 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 260 (accept_3_2 31 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 81 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 260 (accept_3_2 28 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 260 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 81 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 260 (accept_3_2 25 81 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 260 (accept_3_2 22 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 260 (Polychromatic418967fa.accept_25_20_6_10_1_15841 20 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 260 (accept_3_2 19 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 260 (accept_3_2 16 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 260 (Polychromatic418967fa.accept_17_15_13_5_1_9877 15 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 14 81 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 260 (accept_3_2 13 81 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 260 (accept_3_2 10 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 260 (Polychromatic418967fa.accept_17_9_13_5_1_3512 9 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 81 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 260 (accept_3_2 7 81 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 81 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 260 (accept_3_2 4 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 260 (Polychromatic418967fa.accept_23_2_12_7_1_15840 2 81 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 260 (accept_3_2 1 81 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 260 (allA_succ_of_accept 79 80 260 (accept_3_2 79 80 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 80 260 2 39 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 80 260 (Polychromatic418967fa.accept_17_9_12_5_1_219 77 80 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 80 260 4 19 20 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 80 260 5 15 16 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 80 260 2 37 40 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 260 (accept_3_2 73 80 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 260 4 18 20 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 260
  (Polychromatic418967fa.accept_19_14_4_13_1_7779 71 80 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 260 10 7 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 260 (Polychromatic418967fa.accept_24_21_8_20_1_14133 69 80 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 260 4 17 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 260 (accept_3_2 67 80 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 260 2 33 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 80 260 5 13 16 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 80 260 4 16 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 260 (Polychromatic418967fa.accept_19_6_4_13_1_2329 63 80 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 260 2 31 40 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 260 (accept_3_2 61
  80 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 260 20 3 4 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 260
  (Polychromatic418967fa.accept_11_4_3_7_1_828 59 80 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 80 260 2 29 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 80 260 (Polychromatic418967fa.accept_21_15_17_8_1_9937 57 80 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 80 260 4 14 20 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 80 260 5 11 16 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 80 260 2 27 40 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 80 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 80 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 80 260 4 13 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 80 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 80 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 260 10 5 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 260 (accept_3_2 49 80 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 80 260 4 12 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 80 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 80 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 260 2 23 40 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 80 260 5 9 16 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 80 260 4 11 20 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 260 (accept_3_2 43 80 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 260 2 21 40 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 260
  (Polychromatic418967fa.accept_17_7_12_5_1_1580 41 80 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 260 20 2 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 80 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 260 2 19 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 260 (accept_3_2 37 80 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 260 4 9 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 80 260 5 7 16 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 34 80 260 2 17 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 80 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 260 4 8 20 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 260 (accept_3_2 31 80 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 260 10 3 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 260
  (Polychromatic418967fa.accept_19_10_4_13_1_14484 29 80 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 260 4 7 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 260 (Polychromatic418967fa.accept_17_10_12_5_1_6028 27 80 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 260 2 13 40 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 80 260 5 5 16 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 80 260 4 6 20 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 80 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 80 260 2 11 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 80 260 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 80 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 260 20 1 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 260 (accept_3_2 19 80 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 260 2 9 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 80 260 (Polychromatic418967fa.accept_19_17_4_13_1_4828 17 80
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 260 4 4 20 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 80 260 5 3 16 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 80 260 2 7 40 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 260 (accept_3_2 13
  80 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 260 4 3 20 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 80 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 260 10 1 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 80 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 260 4 2 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 260 (accept_3_2 7 80 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 80 260 2 3 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 80 260 5 1 16 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 80 260 4 1 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 80 260 (Polychromatic418967fa.accept_19_3_4_13_1_4864 3 80 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 260 2 1 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 260 (accept_3_2 1 80 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 260 (allA_of_3_0 79 79 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 260
  (allA_succ_of_accept 77 78 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 78 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 260 2 38 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 78 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 75
  78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 260 2 37 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 260 (accept_3_2 73
  78 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 260 2 36 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 260
  (Polychromatic418967fa.accept_16_7_14_4_1_1362 71 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 260 2 35 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 78 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 69 78 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 260 2 34 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 260 (accept_3_2 67 78 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 260 2 33 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 78 260 13 5 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 78 260 2 32 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 260 2 31 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 260 (accept_3_2 61 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 260 2 30 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 78 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 260 2 29 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 260 2 28 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 78 260 (accept_3_2 55 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 260 2 27 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 260 (Polychromatic418967fa.accept_15_8_3_5_1_608 53 78 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 260 26 2 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 51
  78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 260 2 25 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 260 (accept_3_2 49
  78 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 260 2 24 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 78 260 2 23 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 78 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 78 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 260 2 22 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 260 (accept_3_2 43 78 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 260 2 21 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 41
  78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 260 2 20 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 260 13 3 6 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 260 2 19 39 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 260
  (accept_3_2 37 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 260 2 18 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 260
  (Polychromatic418967fa.accept_19_16_2_13_1_13234 35 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 78 260 2 17 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 78 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 78 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 260 2 16 39 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 260 (accept_3_2 31 78 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 260 2 15 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 260 2 14 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 78 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 78 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 260 26 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 260 (accept_3_2 25 78 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 260 2 12 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 78 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 260 2 11 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 260 2 10 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 78 260 (accept_3_2 19 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 260 2 9 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 78 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 260 2 8 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 260 2 7 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 78 260 13 1 6 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 78 260 2 6 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 78 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 260 2 5 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 78 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 78 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 260 2 4 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 260 (accept_3_2 7 78 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 78 260 2 3 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 78 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 78 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 260 2 2 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 78
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 260 2 1 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 260 (accept_3_2 1 78
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 260
  (allA_succ_of_accept 76 77 260 (accept_3_2 76 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 260 (accept_3_2 73 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 260 (Polychromatic418967fa.accept_15_12_2_5_1_3939 72 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 260
  (Polychromatic418967fa.accept_14_1_7_8_1_2063 71 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 260 (accept_3_2 70 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 260 (Polychromatic418967fa.accept_18_14_5_8_1_1880 68 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 260 (accept_3_2 67 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 77 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 260
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 260 (accept_3_2 64 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 260 (accept_3_2 61 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 260
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 59 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 260 (accept_3_2 58 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 260 (accept_3_2 55 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 260 (Polychromatic418967fa.accept_16_6_13_4_1_643 54 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 260
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 53 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 260 (accept_3_2 52 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 260 (accept_3_2 49 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 260 (accept_3_2 46 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 260 (Polychromatic418967fa.accept_15_14_2_5_1_1272 44 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 260 (accept_3_2 43 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 77 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 260
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 260 (accept_3_2 40 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 260 (accept_3_2 37 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 260 (Polychromatic418967fa.accept_21_15_14_8_1_6826 36 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 260
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 35 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 260 (accept_3_2 34 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 260 (Polychromatic418967fa.accept_18_14_5_8_1_1880 32 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 260 (accept_3_2 31 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 260 (accept_3_2 28 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 260 (accept_3_2 25 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 260
  (Polychromatic418967fa.accept_16_7_13_4_1_1348 23 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 260 (accept_3_2 22 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 260 (accept_3_2 19 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 260 (Polychromatic418967fa.accept_15_3_2_5_1_2980 18 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 260
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 260 (accept_3_2 16 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 260 (accept_3_2 13 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 260 (accept_3_2 10 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 260 (Polychromatic418967fa.accept_16_8_13_4_1_3258 8 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 260 (accept_3_2 7 77 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 260
  (Polychromatic418967fa.accept_21_5_14_8_1_6818 5 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 260 (accept_3_2 4 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 260 (accept_3_2 1 77 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 260 (allA_of_3_0 76 76 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 260 (allA_succ_of_accept 74 75
  260 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 260 (accept_3_2 73 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 260 (Polychromatic418967fa.accept_16_8_11_4_1_3290 72 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 75 260 5 14 15 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 75 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 260 (accept_3_2 67 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 75 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 75 260 5 13 15 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 260 (accept_3_2 64 75 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 75 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 260 (accept_3_2 61 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75
  260 5 12 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  75 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 260 (accept_3_2 58 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 57 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 75 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 260 5 11 15 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 75 260
  (Polychromatic418967fa.accept_12_6_3_8_1_512 54 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 260 (accept_3_2 52 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 75 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 75 260 5 10 15 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 260 (accept_3_2 49 75 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 75 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 260 (accept_3_2 46 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75
  260 5 9 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  75 260 (Polychromatic418967fa.accept_16_12_11_4_1_1359 44 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 75 260 (accept_3_2 43 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 260 5 8 15 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 75 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 260 (accept_3_2 37 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 260 (Polychromatic418967fa.accept_19_17_18_13_1_9126 36 75 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 75 260 5 7 15 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 260 (accept_3_2 34 75 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 260 (accept_3_2 31 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75
  260 5 6 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  75 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 75 260 (accept_3_2 28 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 260 (Polychromatic418967fa.accept_17_9_7_5_1_1566 26 75 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75 260 5 5 15 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 75 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 260 (accept_3_2 22 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 260 (Polychromatic418967fa.accept_22_21_9_18_1_15839 21 75 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 260 5 4 15 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 260 (accept_3_2 19 75 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 75 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 260 (accept_3_2 16 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75
  260 5 3 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  75 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 75 260 (accept_3_2 13 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 260 (Polychromatic418967fa.accept_16_12_11_4_1_1359 12 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 260 5 2 15 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 75 260
  (Polychromatic418967fa.accept_16_9_11_4_1_3194 9 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 260 (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 260 (accept_3_2 7 75 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 75 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 260 5 1 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 260 (accept_3_2 4 75 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 260 (accept_3_2 1 75 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 260 (allA_succ_of_accept
  73 74 260 (accept_3_2 73 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 260 2 36 37 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 71 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 260 2 35 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 74 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 260 2 34 37 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 260 (accept_3_2 67 74 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 260 2 33 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 65
  74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 260 2 32 37 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 260
  (Polychromatic418967fa.accept_19_6_17_13_1_2323 63 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 260 2 31 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 74 260 (accept_3_2 61 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 74 260 2 30 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 74 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 74 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 260 2 29 37 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 260 2 28 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 260 (accept_3_2 55 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 260 2 27 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 74 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 260 2 26 37 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 260 2 25 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 260 (accept_3_2 49 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 260 2 24 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 74 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 260 2 23 37 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 260 2 22 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 74 260 (accept_3_2 43 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 260 2 21 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 74 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 260 2 20 37 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 260 2 19 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 74 260 (accept_3_2 37 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 260 2 18 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 74 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 74 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 260 2 17 37 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 260 2 16 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 260 (accept_3_2 31 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 260 2 15 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 74 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 260 2 14 37 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 260
  (Polychromatic418967fa.accept_25_2_24_10_1_15838 27 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 74 260 2 13 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 74 260 (accept_3_2 25 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 260 2 12 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 74 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 260 2 11 37 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 260 2 10 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 260 (accept_3_2 19 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 260 2 9 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 74 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 260 2 8 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 15
  74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 260 2 7 37 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 260 (accept_3_2 13
  74 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 260 2 6 37 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 74 260 2 5 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 74 260 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 74 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 260 2 4 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 260 (accept_3_2 7 74 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 260 2 3 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 74 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 260 2 2 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 74
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 260 2 1 37 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 260 (accept_3_2 1 74
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 260 (allA_of_3_0 73 73 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 260 (allA_succ_of_accept 71 72 260
  (Polychromatic418967fa.accept_14_1_2_8_1_655 71 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 260 2 35 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 72 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 72 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 260 4 17 18 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 260 (accept_3_2 67 72 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 260 2 33 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 260 (Polychromatic418967fa.accept_16_1_8_4_1_4334
  65 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 260 4 16 18 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 260
  (Polychromatic418967fa.accept_16_15_8_4_1_1355 63 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 260 2 31 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 72 260 (accept_3_2 61 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 260 4 15 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 72 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 260 2 29 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 260 (Polychromatic418967fa.accept_14_1_2_8_1_655 57
  72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 260 4 14 18 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 260 (accept_3_2 55
  72 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 260 2 27 36 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 260
  (Polychromatic418967fa.accept_15_8_12_5_1_2987 53 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 260 4 13 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 51 72 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 260 2 25 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 260 (accept_3_2 49 72 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 260 4 12 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 260 (Polychromatic418967fa.accept_15_2_12_5_1_2107 47 72 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 260 2 23 36 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 260 4 11 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 260 (accept_3_2 43 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  260 2 21 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 72 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 260 4 10 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 72 260 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 72 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 260 2 19 36 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 260 (accept_3_2 37 72 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 260 4 9 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 260 (Polychromatic418967fa.accept_16_3_8_4_1_3279
  35 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 260 2 17 36 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 260
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 33 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 260 4 8 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 260 (accept_3_2 31 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  260 2 15 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 72 260 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 260 4 7 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 260 2 13 36 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 260 (accept_3_2 25 72 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 260 4 6 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 72 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 260 2 11 36 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 260
  (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 260 4 5 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 260 (accept_3_2 19 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  260 2 9 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 260 4 4 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 260 (Polychromatic418967fa.accept_14_1_2_8_1_655 15 72 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 260 2 7 36 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 260 (accept_3_2 13 72 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 260 4 3 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 260 (Polychromatic418967fa.accept_16_11_8_4_1_2234 11 72 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 260 2 5 36 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 260
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 260 4 2 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 260 (accept_3_2 7 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 260
  2 3 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  260 (Polychromatic418967fa.accept_16_5_8_4_1_5418 5 72 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 260 4 1 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 260 2 1 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 260 (accept_3_2 1 72 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 260 (allA_succ_of_accept 70 71 260 (accept_3_2 70 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 68 71 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 260 (accept_3_2 67 71 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 260 (Polychromatic418967fa.accept_15_6_11_5_1_168
  66 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 260
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 65 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 260 (accept_3_2 64 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 260 (accept_3_2 61 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 260 (Polychromatic418967fa.accept_16_12_7_4_1_687 60 71 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 260 (accept_3_2 58 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 260 (Polychromatic418967fa.accept_16_8_7_4_1_2217 56 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 260 (accept_3_2 55 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 260 (Polychromatic418967fa.accept_15_9_11_5_1_1283 54 71 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 260
  (Polychromatic418967fa.accept_11_9_5_7_1_815 53 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 260 (accept_3_2 52 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 260 (accept_3_2 49 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 260 (Polychromatic418967fa.accept_22_4_5_18_1_14203 48 71 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 260
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 260 (accept_3_2 46 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 260 (Polychromatic418967fa.accept_14_2_1_8_1_650 44 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 260 (accept_3_2 43 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 42 71 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 260
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 41 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 260 (accept_3_2 40 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 260 (accept_3_2 37 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 71 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 260 (accept_3_2 34 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 260 (Polychromatic418967fa.accept_15_2_11_5_1_1266 32 71 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 260 (accept_3_2 31 71 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 260 (Polychromatic418967fa.accept_14_2_1_8_1_650 30 71 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 260
  (Polychromatic418967fa.accept_16_13_7_4_1_3248 29 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 260 (accept_3_2 28 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 260 (accept_3_2 25 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 260 (Polychromatic418967fa.accept_15_9_11_5_1_1283 24 71 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 260
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 23 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 260 (accept_3_2 22 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 260 (accept_3_2 19 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 260 (Polychromatic418967fa.accept_19_18_14_13_1_6341 18 71 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 260
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 260 (accept_3_2 16 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 260 (accept_3_2 13 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 260 (Polychromatic418967fa.accept_16_12_7_4_1_687 12 71 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 260 (accept_3_2 10 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 260 (accept_3_2 7 71 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 6 71 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 260
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 5 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 260 (accept_3_2 4 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 71 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 260 (accept_3_2 1 71 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 260
  (allA_of_3_0 70 70 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 260 (allA_succ_of_accept 68 69 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 260 (accept_3_2 67 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 260 (accept_3_2 64 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 260 (Polychromatic418967fa.accept_14_7_13_8_1_2067 63 69 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 260
  (Polychromatic418967fa.accept_19_5_12_13_1_9115 62 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 260 (accept_3_2 61 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 260 (Polychromatic418967fa.accept_16_12_5_4_1_3275 60 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 260 (accept_3_2 58 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 69 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 260 (accept_3_2 55 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 260 (accept_3_2 52 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 69 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 260 (accept_3_2 49 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 260 (accept_3_2 46 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 260 (Polychromatic418967fa.accept_21_3_6_8_1_11449 45 69 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 260 (accept_3_2 43 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 260 (accept_3_2 40 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 69 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 260 (accept_3_2 37 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 260 (Polychromatic418967fa.accept_21_15_6_8_1_9888 36 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 260 (accept_3_2 34 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 260 (accept_3_2 31 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 260 (accept_3_2 28 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 69 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 260 (accept_3_2 25 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 260 (Polychromatic418967fa.accept_16_8_5_4_1_674 24 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 260 (accept_3_2 22 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 260 (accept_3_2 19 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 260 (accept_3_2 16 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 260 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 69 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 260 (accept_3_2 13 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 260 (accept_3_2 10 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 260
  (Polychromatic418967fa.accept_16_8_5_4_1_674 8 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 260 (accept_3_2 7 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  260 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 260 (accept_3_2 4 69 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 69 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 69
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 260 (accept_3_2 1 69 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 260 (allA_succ_of_accept 67 68
  260 (accept_3_2 67 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 260 2 33 34 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 260 4 16 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105 63 68 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 260 2 31 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 260 (accept_3_2 61 68 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 260 4 15 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 68 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 260 2 29 34 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 260 4 14 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 260 (accept_3_2 55 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  260 2 27 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 68 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 260 4 13 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 68 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 260 2 25 34 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 260 (accept_3_2 49 68 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 260 4 12 17 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 260 2 23 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 68 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 68 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 260 4 11 17 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 260 (accept_3_2 43 68 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 260 2 21 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 41
  68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 260 4 10 17 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 260 2 19 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 68 260 (accept_3_2 37 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 68 260 4 9 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 68 260 (Polychromatic418967fa.accept_19_16_11_13_1_4944 35 68 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 260 2 17 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 33
  68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 260 4 8 17 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 260 (accept_3_2 31
  68 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 260 2 15 34 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 68 260 4 7 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 68 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 68 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 260 2 13 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 260 (accept_3_2 25 68 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 260 4 6 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 68 260 (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 68 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 260 2 11 34 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 260 4 5 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 260 (accept_3_2 19 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  260 2 9 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 260 4 4 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 68 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 260 2 7 34 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 260 (accept_3_2 13 68 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 260 4 3 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 68 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 260 2 5 34 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 260
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 260 4 2 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 260 (accept_3_2 7 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 260
  2 3 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  260 (Polychromatic418967fa.accept_18_5_14_8_1_2966 5 68 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 68 260 4 1 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 68 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 68 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 260 2 1 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 260 (accept_3_2 1 68 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 68 260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  67 260 (allA_of_3_0 67 67 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 260 (allA_succ_of_accept 65 66
  260 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 260 2 32 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 66 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 66 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 260 2 31 33 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 260 (accept_3_2 61 66 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 260 2 30 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 59
  66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 260 2 29 33 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 260 2 28 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 66 260 (accept_3_2 55 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 260 2 27 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 66 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 260 2 26 33 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 260 2 25 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 66 260 (accept_3_2 49 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 260 2 24 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 66 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 260 2 23 33 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 260 2 22 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 260 (accept_3_2 43 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 260 2 21 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 66 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 260 2 20 33 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 260 2 19 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 66 260 (accept_3_2 37 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 260 2 18 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 260 (Polychromatic418967fa.accept_21_14_3_8_1_3806 35 66 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 260 2 17 33 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 260 2 16 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 66 260 (accept_3_2 31 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 260 2 15 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 66 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 260 2 14 33 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 260 2 13 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 66 260 (accept_3_2 25 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 260 2 12 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 66 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 260 2 11 33 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 260 2 10 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 66 260 (accept_3_2 19 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 260 2 9 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 260 (Polychromatic418967fa.accept_19_17_9_13_1_6325 17 66 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 260 2 8 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 260 2 7 33 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 260 (accept_3_2 13
  66 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 260 2 6 33 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 260 2 5 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 66 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 66 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 260 2 4 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 260 (accept_3_2 7 66 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 66 260 2 3 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 66 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 260 2 2 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  66 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 260 2 1 33 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 260 (accept_3_2 1 66
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 260 (allA_succ_of_accept 64 65 260
  (accept_3_2 64 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 65 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 260 (accept_3_2 61 65 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 65 260 5 12 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 65 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 65 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 260 (accept_3_2 58 65 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 260
  (Polychromatic418967fa.accept_16_8_1_4_1_6622 56 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 65 260 5 11 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 65 260 (Polychromatic418967fa.accept_22_10_21_18_1_12704 54 65 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 53
  65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 65 260 13 4 5 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 65 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 65 260 5 10 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 65 260 (accept_3_2 49 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 47 65 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 260 (accept_3_2 46 65 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 45 65 260 5 9 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 65 260 (Polychromatic418967fa.accept_16_12_1_4_1_5403 44 65 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 260 (accept_3_2 43 65 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 260 5 8 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 65 260 13 3 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 65 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 65 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 260 (accept_3_2 37 65 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 65 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 65 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 260 5 7 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 260 (accept_3_2 34 65 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 260 (accept_3_2 31 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 65
  260 5 6 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  65 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 65 260 (accept_3_2 28 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 65 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 65 260 13 2 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 65 260 5 5 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 65 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 65 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 260 (accept_3_2 22 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 65 260 5 4 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 65 260 (accept_3_2 19 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 65 260 (Polychromatic418967fa.accept_19_18_8_13_1_6303 18 65 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 65 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 260 (accept_3_2 16 65 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 65 260 5 3 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 65 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 65 260 13 1 5 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 65 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 65 260 (Polychromatic418967fa.accept_22_11_21_18_1_15837 11 65 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 65 260 5 2 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 65 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 260
  (Polychromatic418967fa.accept_16_8_1_4_1_6622 8 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 260 (accept_3_2 7 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  260 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 65 260 5 1 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 65 260 (accept_3_2 4 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 65 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 260 (accept_3_2 1 65 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 260
  (allA_of_3_0 64 64 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 260 (allA_succ_of_accept 62 63 260
  (Polychromatic418967fa.accept_14_6_7_8_1_624 62 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 260 (accept_3_2 61 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 260 (Polychromatic418967fa.accept_16_12_15_4_1_5422 60 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 260 (accept_3_2 58 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 260 (Polychromatic418967fa.accept_14_1_7_8_1_2063 57 63 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 260
  (Polychromatic418967fa.accept_16_8_15_4_1_5402 56 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 260 (accept_3_2 55 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 260 (accept_3_2 52 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 260
  (Polychromatic418967fa.accept_19_12_6_13_1_2305 50 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 260 (accept_3_2 49 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 260 (Polychromatic418967fa.accept_11_4_8_7_1_819 48 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 260 (accept_3_2 46 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 260 (Polychromatic418967fa.accept_19_7_6_13_1_6322 45 63 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 260
  (Polychromatic418967fa.accept_16_12_15_4_1_5422 44 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 260 (accept_3_2 43 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 260 (accept_3_2 40 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 63 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 260
  (Polychromatic418967fa.accept_15_8_3_5_1_608 38 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 260 (accept_3_2 37 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 260 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 260 (accept_3_2 34 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 260 (Polychromatic418967fa.accept_23_10_17_7_1_5931 33 63 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 260
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 32 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 260 (accept_3_2 31 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 260 (accept_3_2 28 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 260
  (Polychromatic418967fa.accept_11_4_8_7_1_819 26 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 260 (accept_3_2 25 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 260 (accept_3_2 22 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 260 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 63 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 260
  (Polychromatic418967fa.accept_14_6_7_8_1_624 20 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 260 (accept_3_2 19 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 260 (accept_3_2 16 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 260 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 63 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 260
  (Polychromatic418967fa.accept_16_14_15_4_1_3268 14 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 260 (accept_3_2 13 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 260 (Polychromatic418967fa.accept_16_12_15_4_1_5422 12 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 260 (accept_3_2 10 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 63 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 260
  (Polychromatic418967fa.accept_15_8_3_5_1_608 8 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 260 (accept_3_2 7 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  260 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 260 (accept_3_2 4 63 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 260 (Polychromatic418967fa.accept_15_2_3_5_1_2991 2
  63 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 260 (accept_3_2 1 63 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 260 (allA_succ_of_accept 61 62 260
  (accept_3_2 61 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 260 2 30 31 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 59 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 260 2 29 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 260 (Polychromatic418967fa.accept_15_12_2_5_1_3939 57 62 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 260 2 28 31 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 260 (accept_3_2 55 62 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 260 2 27 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 53
  62 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 260 2 26 31 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 260 2 25 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 260 (accept_3_2 49 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 260 2 24 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 62 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 260 2 23 31 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 260
  (Polychromatic418967fa.accept_19_7_5_13_1_3493 45 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 260 2 22 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 260 (accept_3_2 43 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 260 2 21 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 62 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 260 2 20 31 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 260
  (Polychromatic418967fa.accept_16_7_14_4_1_1362 39 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 260 2 19 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 260 (accept_3_2 37 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 260 2 18 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 62 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 260 2 17 31 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 260 2 16 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 260 (accept_3_2 31 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 260 2 15 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 62 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 260 2 14 31 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 260
  (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 260 2 13 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 260 (accept_3_2 25 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 260 2 12 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 62 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 260 2 11 31 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 260
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 260 2 10 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 260 (accept_3_2 19 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 260 2 9 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 62 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 260 2 8 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 260 (Polychromatic418967fa.accept_16_15_14_4_1_6649
  15 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 260 2 7 31 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 260 (accept_3_2 13
  62 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 260 2 6 31 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 62 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 260 2 5 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 62 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 260 2 4 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 260 (accept_3_2 7 62 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 260 2 3 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 62 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 260 2 2 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 260 (Polychromatic418967fa.accept_15_3_2_5_1_2980 3
  62 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 260 2 1 31 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 260 (accept_3_2 1 62
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 260 (allA_of_3_0 61 61 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 260 (allA_succ_of_accept 59 60 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 60 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 260 2 29 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 60 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 260 4 14 15 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 60 260 5 11 12 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 260 2 27 30 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 260
  (Polychromatic418967fa.accept_11_9_5_7_1_815 53 60 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 60 260 4 13 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 60 260 (Polychromatic418967fa.accept_16_3_12_4_1_170 51 60 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 260 10 5 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 260 (accept_3_2 49 60 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 60 260 4 12 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 60 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 60 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 260 2 23 30 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 260 5 9 12 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 260 4 11 15 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 260 (accept_3_2 43 60 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 260 2 21 30 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 60 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 260 20 2 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 260 2 19 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 260 (accept_3_2 37 60 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 260 4 9 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 260 5 7 12 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 260 2 17 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 60 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 260 4 8 15 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 260 (accept_3_2 31 60 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 260 10 3 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 29
  60 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 260 4 7 15 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 260
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 60 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 60 260 2 13 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 60 260 5 5 12 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 60 260 4 6 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 60 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 60 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 260 2 11 30 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 260 20 1 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 260 (accept_3_2 19 60 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  260 2 9 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 260 4 4 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 60 260 5 3 12 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 60 260 2 7 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 60 260 (accept_3_2 13 60 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 260 4 3 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 260 10 1 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 60 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 260 4 2 15 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 260 (accept_3_2 7 60 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 260 2 3 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 260 5 1 12 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 60 260 4 1 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 260 2 1 30 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 260 (accept_3_2 1 60
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 260 (allA_succ_of_accept 58 59 260
  (accept_3_2 58 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 260 (accept_3_2 55 59 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 260 (accept_3_2 52 59
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 260 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 260 (accept_3_2 49 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 260 (accept_3_2 46 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 260 (accept_3_2 43 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 41 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 260 (accept_3_2 40 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 260 (accept_3_2 37 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 260 (Polychromatic418967fa.accept_18_17_5_8_1_1898 35 59 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 260 (accept_3_2 34 59 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 260 (accept_3_2 31 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 260 (accept_3_2 28 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 260 (accept_3_2 25 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 260 (accept_3_2 22 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 260 (accept_3_2 19 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 260 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 59 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 260 (accept_3_2 16 59 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 260
  (Polychromatic418967fa.accept_11_3_4_7_1_114 14 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 260 (accept_3_2 13 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 260 (accept_3_2 10 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 260
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 260 (accept_3_2 7 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  260 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 59 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 59 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 260 (accept_3_2 4 59 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 59
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 260 (accept_3_2 1 59 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 58 260 (allA_of_3_0 58 58 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 260
  (allA_succ_of_accept 56 57 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 57 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 260 (accept_3_2 55 57 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 57 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 260 (accept_3_2 52 57
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 57 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 260 (accept_3_2 49 57 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 260 (Polychromatic418967fa.accept_18_12_3_8_1_6817 48 57 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 260 (accept_3_2 46 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  57 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 57 260 (Polychromatic418967fa.accept_14_2_1_8_1_650 44 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 260 (accept_3_2 43 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 260 (accept_3_2 40 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  57 260 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 57 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 260 (accept_3_2 37 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 57 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 260 (accept_3_2 34 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  57 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 57 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 260 (accept_3_2 31 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 57 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 260 (accept_3_2 28 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  57 260 (Polychromatic418967fa.accept_16_11_9_4_1_5438 27 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 57 260 (Polychromatic418967fa.accept_21_5_15_8_1_9935 26 57 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 260 (accept_3_2 25 57 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 57 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 260 (accept_3_2 22 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  57 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 57 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 260 (accept_3_2 19 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 57 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 260 (accept_3_2 16 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  57 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 57 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 260 (accept_3_2 13 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 260 (Polychromatic418967fa.accept_16_12_9_4_1_4345 12 57 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 260 (accept_3_2 10 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  57 260 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 57 260 (Polychromatic418967fa.accept_15_8_12_5_1_2987 8 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 260 (accept_3_2 7 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 57 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 260 (accept_3_2 4 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57
  260 (Polychromatic418967fa.accept_17_3_6_5_1_8669 3 57 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 57 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 260 (accept_3_2 1 57 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 57 260))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 260
  (allA_succ_of_accept 55 56 260 (accept_3_2 55 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 56
  260 2 27 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 56 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 53 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 56 260 4 13 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 56 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 56 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 260 2 25 28 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 260 (accept_3_2 49 56 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 260 4 12 14 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 260
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 260 2 23 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 56 260 (Polychromatic418967fa.accept_16_13_8_4_1_3250 45 56 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 260 4 11 14 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 260 (accept_3_2 43 56 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 260 2 21 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 41
  56 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 260 4 10 14 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 260 2 19 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 56 260 (accept_3_2 37 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 56 260 4 9 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 56 260 (Polychromatic418967fa.accept_16_3_8_4_1_3279 35 56 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 260 2 17 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 33
  56 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 260 4 8 14 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 260 (accept_3_2 31
  56 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 260 2 15 28 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 260
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 29 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 260 4 7 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 260 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 56 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 260 2 13 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 260 (accept_3_2 25 56 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 260 4 6 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 56 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 260 2 11 28 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 260 4 5 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 260 (accept_3_2 19 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  260 2 9 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 260 4 4 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 56 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 260 2 7 28 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 260 (accept_3_2 13 56 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 260 4 3 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 260 (Polychromatic418967fa.accept_16_11_8_4_1_2234 11 56 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 260 2 5 28 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 260
  (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 260 4 2 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 260 (accept_3_2 7 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 260
  2 3 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  260 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 260 4 1 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 56 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 260 2 1 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 260 (accept_3_2 1 56 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 260)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 260 (allA_of_3_0 55
  55 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 260 (allA_succ_of_accept 53 54 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 260 2 26 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 54 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 51 54 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 260 2 25 27 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 260 (accept_3_2 49 54 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 260 2 24 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 260 (Polychromatic418967fa.accept_11_3_10_7_1_129
  47 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 260 2 23 27 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 260 2 22 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 54 260 (accept_3_2 43 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 260 2 21 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 54 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 54 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 260 2 20 27 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 260 2 19 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 54 260 (accept_3_2 37 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 260 2 18 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 260 (Polychromatic418967fa.accept_16_3_6_4_1_679 35 54 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 260 2 17 27 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 260 2 16 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 54 260 (accept_3_2 31 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 260 2 15 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 260 (Polychromatic418967fa.accept_15_14_9_5_1_3932 29 54 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 260 2 14 27 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 260 2 13 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 54 260 (accept_3_2 25 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 260 2 12 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 260 (Polychromatic418967fa.accept_17_6_3_5_1_3657 23 54 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 260 2 11 27 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 260 2 10 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 54 260 (accept_3_2 19 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 260 2 9 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 54 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 260 2 8 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  54 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 260 2 7 27 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 260 (accept_3_2 13
  54 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 260 2 6 27 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 54 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 260 2 5 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 54 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 54 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 260 2 4 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 260 (accept_3_2 7 54 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 54 260 2 3 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 54 260 (Polychromatic418967fa.accept_16_5_6_4_1_3211 5 54 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 260 2 2 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 54
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 260 2 1 27 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 260 (accept_3_2 1 54
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 260))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 260 (allA_succ_of_accept 52 53 260 (accept_3_2 52 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 53 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 260 (accept_3_2 49 53 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105
  48 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 260 (accept_3_2 46 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 260 (Polychromatic418967fa.accept_15_14_8_5_1_2104 44 53 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 260 (accept_3_2 43 53 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 260 (Polychromatic418967fa.accept_15_12_8_5_1_5048 42 53
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 260
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 260 (accept_3_2 40 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 53 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 260 (accept_3_2 37 53 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 260 (Polychromatic418967fa.accept_19_17_15_13_1_7794 36 53 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 260
  (Polychromatic418967fa.accept_11_2_9_7_1_124 35 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 260 (accept_3_2 34 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 53 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 260 (accept_3_2 31 53 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 260 (Polychromatic418967fa.accept_22_8_9_18_1_3276 30 53
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 260
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 260 (accept_3_2 28 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 53 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 260 (accept_3_2 25 53 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 260
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 260 (accept_3_2 22 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 260 (Polychromatic418967fa.accept_17_3_2_5_1_2556 20 53 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 260 (accept_3_2 19 53 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 53 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 260 (accept_3_2 16 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 53 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 260 (accept_3_2 13 53 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 260
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 260 (accept_3_2 10 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 260 (Polychromatic418967fa.accept_16_8_5_4_1_674 8 53 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 260 (accept_3_2 7 53 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 260 (Polychromatic418967fa.accept_16_6_5_4_1_4330 6 53 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 260 (accept_3_2 4 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 53 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 260 (accept_3_2 1 53 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 260))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 260 (allA_of_3_0 52 52
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 260 (allA_succ_of_accept 50 51 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 260 (accept_3_2 49 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 260 (accept_3_2 46 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 51 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 260
  (Polychromatic418967fa.accept_15_14_6_5_1_7215 44 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 260 (accept_3_2 43 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 260 (accept_3_2 40 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 51 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 260 (accept_3_2 37 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 260 (Polychromatic418967fa.accept_22_14_7_18_1_15836 36 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 260 (accept_3_2 34 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 260 (Polychromatic418967fa.accept_15_3_6_5_1_2079 33 51 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 260 (accept_3_2 31 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 260 (accept_3_2 28 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 260
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 260 (accept_3_2 25 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 260 (accept_3_2 22 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 260 (accept_3_2 19 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 260 (accept_3_2 16 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 260 (accept_3_2 13 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 260 (accept_3_2 10 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 260 (Polychromatic418967fa.accept_23_9_5_7_1_15835 9 51 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 260
  (Polychromatic418967fa.accept_16_8_3_4_1_3233 8 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 260 (accept_3_2 7 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  260 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 260 (accept_3_2 4 51 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  51 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 260 (accept_3_2 1 51 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 260)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 260 (allA_succ_of_accept 49 50 260 (accept_3_2 49 50 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 260 2 24 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 50 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 50 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 260 2 23 25 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 50 260 5 9 10 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 50 260 2 22 25 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 260 (accept_3_2 43 50 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 260 2 21 25 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 50 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 260 10 4 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 50 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 260 2 19 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 260 (accept_3_2 37 50 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 260 2 18 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 50 260 5 7 10 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 50 260 2 17 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 33
  50 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 260 2 16 25 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 260 (accept_3_2 31
  50 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 260 10 3 5 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 260 2 14 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 50 260 (Polychromatic418967fa.accept_28_27_22_8_1_15834 27 50 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 260 2 13 25 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 50 260 5 5 10 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 50 260 2 12 25 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 260
  (Polychromatic418967fa.accept_11_1_6_7_1_116 23 50 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 260 2 11 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 50 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 50 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 260 10 2 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 260 (accept_3_2 19 50 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 260 2 9 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 50 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 50 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 260 2 8 25 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 50 260 5 3 10 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 50 260 2 7 25 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 260 (accept_3_2 13
  50 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 260 2 6 25 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 50 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 260 10 1 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 260 (Polychromatic418967fa.accept_27_9_23_17_1_15833 9 50 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 260 2 4 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 260 (accept_3_2 7 50 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 260 2 3 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 50 260 5 1 10 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 50 260 2 2 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 50 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 50 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 260 2 1 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 260 (accept_3_2 1 50 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 50 260)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 260 (allA_of_3_0
  49 49 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 260 (allA_succ_of_accept 47 48 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 48 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 260 2 23 24 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 48 260 (Polychromatic418967fa.accept_21_3_6_8_1_11449 45 48 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 260 4 11 12 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 260 (accept_3_2 43 48 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 260 2 21 24 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 41
  48 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 260 4 10 12 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 260
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 48 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 260 2 19 24 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 48 260 (accept_3_2 37 48 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 260 4 9 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 260 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 48 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 260 2 17 24 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 33
  48 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 260 4 8 12 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 260 (accept_3_2 31
  48 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 260 2 15 24 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 48 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 260 4 7 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 48 260 (Polychromatic418967fa.accept_17_10_14_5_1_11167 27 48 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 260 2 13 24 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 260 (accept_3_2 25 48 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 260 4 6 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 48 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 260 2 11 24 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 260
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 48 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 260 4 5 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 260 (accept_3_2 19 48 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  260 2 9 24 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 260 (Polychromatic418967fa.accept_15_2_3_5_1_2991 17 48 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 260 4 4 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 260 2 7 24 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 260 (accept_3_2 13 48 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 260 4 3 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 48 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 260 2 5 24 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 260 4 2 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 260 (accept_3_2 7 48 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 260
  2 3 24 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  260 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 260 4 1 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 48 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 48 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 260 2 1 24 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 260 (accept_3_2 1 48 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 260)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 260 (allA_succ_of_accept 46
  47 260 (accept_3_2 46 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 260 (Polychromatic418967fa.accept_15_14_2_5_1_1272 44 47 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 260 (accept_3_2 43 47 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 41
  47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 260 (accept_3_2 40 47
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 260 (Polychromatic418967fa.accept_6_3_5_2_1_12
  39 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 260 (accept_3_2 37 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 260 (Polychromatic418967fa.accept_19_17_9_13_1_6325 36 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 260 (accept_3_2 34 47 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 260 (accept_3_2 31 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 260 (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 47 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 260 (accept_3_2 28 47 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 260
  (Polychromatic418967fa.accept_11_4_3_7_1_828 26 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 260 (accept_3_2 25 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 260 (accept_3_2 22 47 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 260 (accept_3_2 19 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 47 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 260 (accept_3_2 16 47 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 260 (accept_3_2 13 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 260 (accept_3_2 10 47 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 260
  (Polychromatic418967fa.accept_16_8_15_4_1_5402 8 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 260 (accept_3_2 7 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  260 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 260 (accept_3_2 4 47 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  47 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 260 (accept_3_2 1 47 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 260))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  260 (allA_of_3_0 46 46 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 260 (allA_succ_of_accept 44 45 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 260 (accept_3_2 43 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 260 5 8 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 45 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 39
  45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 260
  (Polychromatic418967fa.accept_16_6_13_4_1_643 38 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 260 (accept_3_2 37 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 260 (Polychromatic418967fa.accept_19_17_7_13_1_4833 36 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 45 260 5 7 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 45 260 (accept_3_2 34 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 45 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 45 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 260 (accept_3_2 31 45 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 260 5 6 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 260 (accept_3_2 28 45
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 260
  (Polychromatic418967fa.accept_21_6_3_8_1_9928 27 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 45 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 260 5 5 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 45 260 (Polychromatic418967fa.accept_16_8_13_4_1_3258 24 45 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 260 (accept_3_2 22 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  45 260 (Polychromatic418967fa.accept_18_3_9_8_1_2977 21 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 45 260 5 4 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 45 260 (accept_3_2 19 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 45 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 260 (accept_3_2 16 45 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 260 5 3 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 260 (Polychromatic418967fa.accept_21_14_3_8_1_3806
  14 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 260 (accept_3_2 13
  45 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 260 5 2 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 260
  (Polychromatic418967fa.accept_16_8_13_4_1_3258 8 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 260 (accept_3_2 7 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 45 260 5 1 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 45 260 (accept_3_2 4 45 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 260 (Polychromatic418967fa.accept_18_3_9_8_1_2977 3 45 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 45 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 260 (accept_3_2 1 45 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 260))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  260 (allA_succ_of_accept 43 44 260 (accept_3_2 43 44 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 260 2 21 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 44 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 260 4 10 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 260 (Polychromatic418967fa.accept_15_9_14_5_1_2086
  39 44 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 260 2 19 22 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 260
  (accept_3_2 37 44 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 260 4 9 11 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 260
  (Polychromatic418967fa.accept_16_3_12_4_1_170 35 44 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 260 2 17 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 44 260 (Polychromatic418967fa.accept_16_1_12_4_1_695 33 44 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 260 4 8 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 260 (accept_3_2 31 44 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 260 2 15 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 260 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 44 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 260 4 7 11 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 44 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 260 2 13 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 44 260 (accept_3_2 25 44 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 44 260 4 6 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 44 260 (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 44 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 260 2 11 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 260 (Polychromatic418967fa.accept_15_6_14_5_1_2976
  21 44 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 260 4 5 11 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 260 (accept_3_2 19
  44 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 260 2 9 22 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 44 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 44 260 4 4 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 44 260 (Polychromatic418967fa.accept_14_1_2_8_1_655 15 44 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 260 2 7 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 260 (accept_3_2 13 44 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 260 4 3 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 260 (Polychromatic418967fa.accept_16_11_12_4_1_3195 11 44 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 260 2 5 22 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 260
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 44 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 260 4 2 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 260 (accept_3_2 7 44 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 260
  2 3 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  260 (Polychromatic418967fa.accept_16_5_12_4_1_4325 5 44 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 44 260 4 1 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 44 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 44 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 260 2 1 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 260 (accept_3_2 1 44 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 44 260)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 260 (allA_of_3_0 43 43
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 260 (allA_succ_of_accept 41 42 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 260 2 20 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 42 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 260 2 19 21 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 260 (accept_3_2 37 42 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 260 2 18 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 35
  42 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 260 2 17 21 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 260 2 16 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 260 (accept_3_2 31 42 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 260 2 15 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 42 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 260 2 14 21 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 260
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 42 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 260 2 13 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 42 260 (accept_3_2 25 42 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 260 2 12 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 260 2 11 21 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 42 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 260 2 10 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 42 260 (accept_3_2 19 42 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 260 2 9 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 260 (Polychromatic418967fa.accept_15_2_12_5_1_2107 17 42 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 260 2 8 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  42 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 260 2 7 21 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 260 (accept_3_2 13
  42 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 260 2 6 21 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 260 2 5 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 42 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 260 2 4 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 260 (accept_3_2 7 42 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 42 260 2 3 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 42 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 260 2 2 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 42
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 260 2 1 21 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 260 (accept_3_2 1 42
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 260)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41
  260 (allA_succ_of_accept 40 41 260 (accept_3_2 40 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 41 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 41 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 260 (accept_3_2 37 41 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 41 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 260
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 35 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 260 (accept_3_2 34 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 260 (Polychromatic418967fa.accept_15_2_11_5_1_1266 32 41 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 260 (accept_3_2 31 41 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 41 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 260
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 260 (accept_3_2 28 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 41 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 260 (accept_3_2 25 41 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 260 (accept_3_2 22 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 260 (accept_3_2 19 41 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 260 (Polychromatic418967fa.accept_33_18_8_29_1_15832 18 41 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 260
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 260 (accept_3_2 16 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 260 (accept_3_2 13 41 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 260 (accept_3_2 10 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 41 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 260 (accept_3_2 7 41 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 260 (accept_3_2 4 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 41 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 260 (accept_3_2 1 41 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 260))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 260 (allA_of_3_0 40 40 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 260 (allA_succ_of_accept 38 39 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 260 (accept_3_2 37 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 260 (Polychromatic418967fa.accept_21_15_18_8_1_6809 36 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 260 (accept_3_2 34 39 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 39 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 260 (accept_3_2 31 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 260 (accept_3_2 28 39 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 39 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 39 260 13 2 3 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 260 (accept_3_2 25 39 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 260 (accept_3_2 22 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  39 260 (Polychromatic418967fa.accept_19_2_1_13_1_15831 21 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 39 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 39 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 260 (accept_3_2 19 39 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 39 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 260 (accept_3_2 16 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  39 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 39 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 39 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 39 260 13 1 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 39 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 12
  39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 260 (accept_3_2 10 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  39 260 (Polychromatic418967fa.accept_18_9_3_8_1_5419 9 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 39 260 (Polychromatic418967fa.accept_16_8_7_4_1_2217 8 39 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 260 (accept_3_2 7 39 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 39 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 39 260 (accept_3_2 4 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39
  260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 39 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 39 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 260 (accept_3_2 1 39 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 39 260))))))))))))))))))))))))))))))))))))))) (allB_succ 38 260 (allA_succ_of_accept 37 38 260
  (accept_3_2 37 38 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38 260 2 18 19 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 38 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 35 38 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 38 260 2 17 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 38 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 38 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 260 2 16 19 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 260 (accept_3_2 31 38 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 260 2 15 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 29
  38 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 38 260 2 14 19 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 38 260
  (Polychromatic418967fa.accept_15_12_8_5_1_5048 27 38 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 38 260 2 13 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 38 260 (accept_3_2 25 38 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 38 260 2 12 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 38 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 38 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 260 2 11 19 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 38 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 260 2 10 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 38 260 (accept_3_2 19 38 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 38 260 2 9 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 38 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 260 2 8 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 15
  38 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 260 2 7 19 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 260 (accept_3_2 13
  38 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 260 2 6 19 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 38 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 260 2 5 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 38 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 260 2 4 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 260 (accept_3_2 7 38 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 260 2 3 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 38 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 260 2 2 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 38
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 260 2 1 19 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 260 (accept_3_2 1 38
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 260)))))))))))))))))))))))))))))))))))))) (allB_succ 37 260
  (allA_of_3_0 37 37 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 260 (allA_succ_of_accept 35 36 260
  (Polychromatic418967fa.accept_19_16_17_13_1_9125 35 36 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 36 260 2 17 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 36 260 (Polychromatic418967fa.accept_15_3_6_5_1_2079 33 36 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 260 4 8 9 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 260 (accept_3_2 31 36 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 260 2 15 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 260 (Polychromatic418967fa.accept_15_14_6_5_1_7215
  29 36 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 260 4 7 9 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 260
  (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 36 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 260 2 13 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 36 260 (accept_3_2 25 36 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 260 4 6 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 260 (Polychromatic418967fa.accept_19_4_17_13_1_4929 23 36 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 260 2 11 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 260 (Polychromatic418967fa.accept_11_10_3_7_1_2564
  21 36 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 260 4 5 9 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 260 (accept_3_2 19
  36 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 260 2 9 18 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 260
  (Polychromatic418967fa.accept_21_17_15_8_1_6799 17 36 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 36 260 4 4 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 36 260 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 36 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 260 2 7 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 260 (accept_3_2 13 36 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 260 4 3 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 36 260 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 36 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 260 2 5 18 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 260
  (Polychromatic418967fa.accept_19_9_17_13_1_2321 9 36 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 260 4 2 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 260 (accept_3_2 7 36 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 260
  2 3 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36
  260 (Polychromatic418967fa.accept_21_5_15_8_1_9935 5 36 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 36 260 4 1 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 36 260 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 36 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 260 2 1 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 260 (accept_3_2 1 36 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 36 260)))))))))))))))))))))))))))))))))))) (allB_succ 35 260 (allA_succ_of_accept 34 35
  260 (accept_3_2 34 35 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 35 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 260 (Polychromatic418967fa.accept_21_11_14_8_1_5256 32 35 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 260 (accept_3_2 31 35 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 260 5 6 7 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 260 (Polychromatic418967fa.accept_14_1_7_8_1_2063 29 35 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 260 (accept_3_2 28 35 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 35 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 260 5 5 7 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 260 (Polychromatic418967fa.accept_16_8_3_4_1_3233 24 35 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 260 (accept_3_2 22 35 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  35 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 260 5 4 7 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 260 (accept_3_2 19
  35 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 260
  (Polychromatic418967fa.accept_19_18_16_13_1_10572 18 35 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 260 (Polychromatic418967fa.accept_16_1_3_4_1_665 17 35 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 260 (accept_3_2 16 35 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 35 260 5 3 7 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 35 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 35 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 260 (accept_3_2 13 35 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 260 (Polychromatic418967fa.accept_16_12_3_4_1_4317 12 35
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 260
  (Polychromatic418967fa.accept_19_11_16_13_1_4853 11 35 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 35 260 5 2 7 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 35 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 260 (Polychromatic418967fa.accept_16_8_3_4_1_3233 8
  35 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 260 (accept_3_2 7 35 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 260 (Polychromatic418967fa.accept_14_6_7_8_1_624 6
  35 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 260 5 1 7 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 260 (accept_3_2 4 35
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 260 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 35 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 35 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 260 (accept_3_2 1 35 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  260))))))))))))))))))))))))))))))))))) (allB_succ 34 260 (allA_of_3_0 34 34 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 260 (allA_succ_of_accept 32 33 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 33 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 260 (accept_3_2 31 33 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 30
  33 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 260 (accept_3_2 28 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 260 (Polychromatic418967fa.accept_21_5_12_8_1_6807 26 33 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 260 (accept_3_2 25 33 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 260 (accept_3_2 22 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 33 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 260 (accept_3_2 19 33 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 33 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 260 (accept_3_2 16 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 260 (Polychromatic418967fa.accept_19_15_14_13_1_2343 15 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 33 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 260 (accept_3_2 13 33 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 260 (accept_3_2 10 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 260 (Polychromatic418967fa.accept_15_8_3_5_1_608 8 33 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 260 (accept_3_2 7 33 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 33 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 260 (accept_3_2 4 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 33 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 260 (accept_3_2 1 33 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 260))))))))))))))))))))))))))))))))) (allB_succ 32 260 (allA_succ_of_accept 31 32 260
  (accept_3_2 31 32 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 260 2 15 16 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 260 4 7 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 260 (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 32 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 260 2 13 16 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 260 (accept_3_2 25 32 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 260 4 6 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 32 260 (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 32 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 260 2 11 16 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 32 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 260 4 5 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 260 (accept_3_2 19 32 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  260 2 9 16 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 32 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 260 4 4 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 32 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 260 2 7 16 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 260 (accept_3_2 13 32 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 260 4 3 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 32 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 260 2 5 16 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 260
  (Polychromatic418967fa.accept_22_9_10_18_1_3230 9 32 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 260 4 2 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 260 (accept_3_2 7 32 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 260
  2 3 16 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 32 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 260 4 1 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 32 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 260 2 1 16 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 260 (accept_3_2 1 32 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 260)))))))))))))))))))))))))))))))) (allB_succ 31 260 (allA_of_3_0 31 31 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 260 (allA_succ_of_accept 29 30 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 30 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 260 2 14 15 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 30 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 30 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 260 2 13 15 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 260 5 5 6 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 260 2 12 15 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 30 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 260 2 11 15 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 30 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 260 10 2 3 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 260 (accept_3_2 19 30 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 260 2 9 15 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 30 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 260 2 8 15 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 260 5 3 6 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 260 2 7 15 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 260 (accept_3_2 13
  30 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 260 2 6 15 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 30 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 260 10 1 3 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 260 2 4 15 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 260 (accept_3_2 7 30 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 260 2 3 15 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 30 260 5 1 6 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 30 260 2 2 15 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 30 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 260 2 1 15 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 260 (accept_3_2 1 30 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 30 260)))))))))))))))))))))))))))))) (allB_succ 29 260 (allA_succ_of_accept 28 29 260
  (accept_3_2 28 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 29 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 260 (accept_3_2 25 29 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 29 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  29 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 260 (accept_3_2 22 29
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 260 (Polychromatic418967fa.accept_6_3_5_2_1_12
  21 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 260
  (Polychromatic418967fa.accept_19_1_10_13_1_4880 20 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 260 (accept_3_2 19 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 260 (Polychromatic418967fa.accept_25_18_4_10_1_15830 18 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 29 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 260 (accept_3_2 16 29 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 260 (accept_3_2 13 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 260 (Polychromatic418967fa.accept_22_11_7_18_1_15829 11 29 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 260 (accept_3_2 10 29 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 260
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 260 (accept_3_2 7 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  260 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 29 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 260 (accept_3_2 4 29 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  29 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 260 (accept_3_2 1 29 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 260))))))))))))))))))))))))))))) (allB_succ 28 260 (allA_of_3_0
  28 28 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 260 (allA_succ_of_accept 26 27 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 260 (accept_3_2 25 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 260 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 260 (accept_3_2 22 27 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 260 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 27 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 260
  (Polychromatic418967fa.accept_11_9_5_7_1_815 20 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 260 (accept_3_2 19 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 260 (accept_3_2 16 27 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 27 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 260
  (Polychromatic418967fa.accept_17_14_10_5_1_8628 14 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 260 (accept_3_2 13 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 260 (accept_3_2 10 27 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 260
  (Polychromatic418967fa.accept_15_8_12_5_1_2987 8 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 260 (accept_3_2 7 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  260 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 260 (accept_3_2 4 27 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 260 (Polychromatic418967fa.accept_18_3_9_8_1_2977 3 27 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 27
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 260 (accept_3_2 1 27 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 260))))))))))))))))))))))))))) (allB_succ 26 260
  (allA_succ_of_accept 25 26 260 (accept_3_2 25 26 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  260 2 12 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 26 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 26 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 260 2 11 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 21 26 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 260 2 10 13 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 260 (accept_3_2 19 26 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 260 2 9 13 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 26 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 26 260 2 8 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 26 260 (Polychromatic418967fa.accept_19_15_7_13_1_11844 15 26 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 260 2 7 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 26 260 13 1 2 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 26 260 2 6 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11
  26 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 260 2 5 13 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 260
  (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 26 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 260 2 4 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 260 (accept_3_2 7 26 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 260
  2 3 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  260 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 26 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 26 260 2 2 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 26 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 26 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 260 2 1 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 260 (accept_3_2 1 26 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 260)))))))))))))))))))))))))) (allB_succ 25 260 (allA_of_3_0 25 25 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 260 (allA_succ_of_accept 23 24 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 260 2 11 12 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 260 4 5 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 260 (accept_3_2 19 24 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  260 2 9 12 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 260 (Polychromatic418967fa.accept_16_1_8_4_1_4334 17 24 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 260 4 4 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 260 (Polychromatic418967fa.accept_16_15_8_4_1_1355 15 24 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 260 2 7 12 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 260 (accept_3_2 13 24 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 260 4 3 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 260 2 5 12 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 260 4 2 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 260 (accept_3_2 7 24 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 260
  2 3 12 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  260 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 260 4 1 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 260 2 1 12 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 260 (accept_3_2 1 24 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 260)))))))))))))))))))))))) (allB_succ 23 260 (allA_succ_of_accept 22 23 260 (accept_3_2 22
  23 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 23 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 260 (accept_3_2 19 23 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 23 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  23 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 260 (accept_3_2 16 23
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 260 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 260 (accept_3_2 13 23 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 23 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 23 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 260 (accept_3_2 10 23 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 260
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 8 23 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 260 (accept_3_2 7 23 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  260 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 23 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 260 (Polychromatic418967fa.accept_21_5_2_8_1_5267 5 23 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 260 (accept_3_2 4 23 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 260 (accept_3_2 1 23 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 260))))))))))))))))))))))) (allB_succ 22 260 (allA_of_3_0 22 22
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 260 (allA_succ_of_accept 20 21 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 21 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 260 (accept_3_2 19 21 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 260 (accept_3_2 16 21 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 21 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 260 (accept_3_2 13 21 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 260 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 21 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 260 (accept_3_2 10 21 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 260
  (Polychromatic418967fa.accept_16_8_5_4_1_674 8 21 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 260 (accept_3_2 7 21 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  260 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 260 (accept_3_2 4 21 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 21 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  21 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 260 (accept_3_2 1 21 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 260))))))))))))))))))))) (allB_succ 20 260 (allA_succ_of_accept
  19 20 260 (accept_3_2 19 20 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 260 2 9 10 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 260
  (Polychromatic418967fa.accept_18_17_2_8_1_6800 17 20 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 260 4 4 5 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 20 260 5 3 4 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 20 260 2 7 10 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 20 260 (accept_3_2 13 20 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20
  260 4 3 5 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  20 260 (Polychromatic418967fa.accept_21_11_20_8_1_8403 11 20 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 20 260 10 1 2 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 20 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 20 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 260 4 2 5 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 260 (accept_3_2 7 20 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 260 2 3 10 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 5 20 260 5 1 4 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 4 20 260 4 1 5 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 20 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 20 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 260 2 1 10 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 260 (accept_3_2 1 20 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 20 260)))))))))))))))))))) (allB_succ 19 260 (allA_of_3_0 19 19 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 18 260 (allA_succ_of_accept 17 18 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 18 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 18 260 2 8 9 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 18 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 15 18 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 18 260 2 7 9 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 260 (accept_3_2 13 18 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 18 260 2 6 9 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 18 260 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 18 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 260 2 5 9 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 18 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 9
  18 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 260 2 4 9 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 260 (accept_3_2 7 18
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 260 2 3 9 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 18 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 18 260 2 2 9 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 18 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 18 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 18 260 2 1 9 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 260 (accept_3_2 1 18 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 18 260)))))))))))))))))) (allB_succ 17 260 (allA_succ_of_accept 16 17 260 (accept_3_2 16 17 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  17 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 17 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 260 (accept_3_2 13 17 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 17 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 260 (accept_3_2 10 17 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 260
  (Polychromatic418967fa.accept_16_8_1_4_1_6622 8 17 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 260 (accept_3_2 7 17 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  260 (Polychromatic418967fa.accept_19_6_17_13_1_2323 6 17 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 260 (accept_3_2 4 17 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 17 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 260 (accept_3_2 1 17 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  260))))))))))))))))) (allB_succ 16 260 (allA_of_3_0 16 16 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  260 (allA_succ_of_accept 14 15 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 15 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 260 (accept_3_2 13 15 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 15 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  15 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 260 5 2 3 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15 260
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 9 15 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 15 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 260 (accept_3_2 7 15 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 15 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 15 260 5 1 3 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 260 (accept_3_2 4 15 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 15 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 15 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 260 (accept_3_2 1 15 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  260))))))))))))))) (allB_succ 14 260 (allA_succ_of_accept 13 14 260 (accept_3_2 13 14 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 14 260 2 6 7 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 14 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 14 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 260 2 5 7 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 260 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9
  14 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 260 2 4 7 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 260 (accept_3_2 7 14
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 260 2 3 7 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 5 14 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 260 2 2 7 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 14 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 260 2 1 7 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 260 (accept_3_2 1 14 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 260)))))))))))))) (allB_succ 13 260 (allA_of_3_0 13 13 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 260 (allA_succ_of_accept 11 12 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 260 2 5 6 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 260
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 12 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 260 4 2 3 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 260 (accept_3_2 7 12 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 260
  2 3 6 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12
  260 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 260 4 1 3 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 12 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 260 2 1 6 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 260 (accept_3_2 1 12 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 260)))))))))))) (allB_succ 11 260 (allA_succ_of_accept 10 11 260 (accept_3_2 10 11 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 260
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 11 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 260 (accept_3_2 7 11 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  260 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 11 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 11 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 260 (accept_3_2 4 11 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  11 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 260 (accept_3_2 1 11 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 260))))))))))) (allB_succ 10 260 (allA_of_3_0 10 10 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 260 (allA_succ_of_accept 8 9 260
  (Polychromatic418967fa.accept_16_8_9_4_1_630 8 9 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 260 (accept_3_2 7 9 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 9 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 260 (accept_3_2 4 9 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 9
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 260 (accept_3_2 1 9 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 260))))))))) (allB_succ 8 260 (allA_succ_of_accept 7 8 260
  (accept_3_2 7 8 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 260 2 3 4 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 260
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 5 8 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 260 4 1 2 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105 3 8 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 260 2 1 4 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 260 (accept_3_2 1 8 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 260)))))))) (allB_succ 7 260 (allA_of_3_0 7 7 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 6 260 (allA_succ_of_accept 5 6 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 6 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 260 2 2 3 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 6
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 260 2 1 3 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 260 (accept_3_2 1 6
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 260)))))) (allB_succ 5 260 (allA_succ_of_accept 4 5 260
  (accept_3_2 4 5 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 260 (accept_3_2 1 5 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 260))))) (allB_succ 4 260 (allA_of_3_0 4 4 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 3 260 (allA_succ_of_accept 2 3 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 3 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 260 (accept_3_2 1 3 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 3 260))) (allB_succ 2 260 (allA_succ_of_accept 1 2 260 (accept_3_2 1 2 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 2 260)) (allB_two
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


