-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch251_Segment000
-- name    : Polychromatic418967fa_Branch251_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:40:10.442447+00:00
-- url     : https://prove2.me/theorems/96ffb3d8-0090-42f7-8e4c-c43adefa7566
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

def Polychromatic418967fa.branch_251_segment_000 : allB 123 251 :=
  allB_succ 122 251 (allA_succ_of_accept 121 122 251 (accept_3_2 121 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 122 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 120 122 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 122 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 119 122
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 122 251 (accept_3_2 118 122
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 122 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 122 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 116 122 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 122 251 (accept_3_2 115 122 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 122 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 114 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 122 251 (Polychromatic418967fa.accept_4_1_2_3_1_9
  113 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 122 251 (accept_3_2
  112 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 122 251
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 122 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 122 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 122 251 (accept_3_2 109 122 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 122 251 (Polychromatic418967fa.accept_16_12_10_11_1_2667 108 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 122 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 107 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 122 251 (accept_3_2 106 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 122 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 122 251 (Polychromatic418967fa.accept_12_8_2_11_1_246 104 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 122 251 (accept_3_2 103 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 122 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 102 122
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 122 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 122 251 (accept_3_2 100 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 122 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 122 251 (Polychromatic418967fa.accept_11_10_1_9_1_2060 98 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 122 251 (accept_3_2 97 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 122 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 122 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 122 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 95 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 122 251 (accept_3_2 94 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 122 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 122 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 122 251 (accept_3_2 91 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 122 251 (Polychromatic418967fa.accept_13_12_5_4_1_3133 90 122 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 122 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 122 251 (accept_3_2 88 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 122 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 122 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 122 251 (accept_3_2 85 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 122 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 122 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 122 251 (accept_3_2 82 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 122 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 122 251 (Polychromatic418967fa.accept_12_8_2_11_1_246 80 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 122 251 (accept_3_2 79 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 122 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 122 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 122 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 122 251 (accept_3_2 76 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 122 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 122 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 74 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 122 251 (accept_3_2 73 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 122 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 122 251
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 71 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 122 251 (accept_3_2 70 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 122 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 122 251 (Polychromatic418967fa.accept_12_8_2_11_1_246 68 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 122 251 (accept_3_2 67 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 122 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 122 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 122 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 122 251 (accept_3_2 64 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 122 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 122 251 (Polychromatic418967fa.accept_13_10_5_4_1_3107 62 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 122 251 (accept_3_2 61 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 122 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 122 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 122 251
  (Polychromatic418967fa.accept_10_9_2_1_1_840 59 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 122 251 (accept_3_2 58 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 122 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 122 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 122 251 (accept_3_2 55 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 122 251 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 122 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 122 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 122 251 (accept_3_2 52 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 122 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 122 251 (Polychromatic418967fa.accept_15_5_2_11_1_1596 50 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 122 251 (accept_3_2 49 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 122 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 122 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 122 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 122 251 (accept_3_2 46 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 122 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 122 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 122 251 (accept_3_2 43 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 122 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 122 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 122 251 (accept_3_2 40 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 122 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 122 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 122 251 (accept_3_2 37 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 122 251 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 251
  (Polychromatic418967fa.accept_13_9_5_4_1_1591 35 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 122 251 (accept_3_2 34 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 122 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 122 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 251 (accept_3_2 31 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 122 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 122 251 (accept_3_2 28 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 122 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 122 251 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 251 (accept_3_2 25 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 122 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 122 251 (accept_3_2 22 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 122 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 122 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 251 (accept_3_2 19 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 122 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 122 251 (accept_3_2 16 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 122 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 122 251 (Polychromatic418967fa.accept_13_1_5_4_1_463 14 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 251 (accept_3_2 13 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 122 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 122 251 (accept_3_2 10 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  122 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 122 251 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 251 (accept_3_2 7 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 122 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 122 251 (accept_3_2 4 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  122 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 122 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 122 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 251 (accept_3_2 1 122 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 122
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 251 (allA_of_3_0 121 121 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 251
  (allA_succ_of_accept 119 120 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 119 120 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 120 251 (accept_3_2 118 120 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 120 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 117 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 251
  (Polychromatic418967fa.accept_13_12_3_4_1_928 116 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 120 251 (accept_3_2 115 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 120 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 114 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 120 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 113 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 120 251 (accept_3_2 112 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 251 (Polychromatic418967fa.accept_11_1_10_9_1_871 111 120
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 120 251
  (Polychromatic418967fa.accept_7_5_1_6_1_163 110 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 120 251 (accept_3_2 109 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 120 251 (Polychromatic418967fa.accept_16_12_8_11_1_2695 108 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 107 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 251 (accept_3_2 106 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 120 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 120
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 120 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 104 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 120 251 (accept_3_2 103 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 120 251 (Polychromatic418967fa.accept_21_18_15_20_1_6076 102 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 120 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 251 (accept_3_2 100 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 251 (Polychromatic418967fa.accept_16_3_8_11_1_2714 99 120
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 120 251
  (Polychromatic418967fa.accept_13_7_3_4_1_459 98 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 120 251 (accept_3_2 97 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 120 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 120 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 251 (accept_3_2 94 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 120 251 (accept_3_2 91 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 120 251 (Polychromatic418967fa.accept_13_12_3_4_1_928 90 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 120 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 251 (accept_3_2 88 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 120 251 (accept_3_2 85 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 120 251 (Polychromatic418967fa.accept_16_4_8_11_1_5961 84 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 120 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 251 (accept_3_2 82 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 251 (Polychromatic418967fa.accept_18_9_12_17_1_6060 81 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 120 251
  (Polychromatic418967fa.accept_17_12_1_13_1_6672 80 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 120 251 (accept_3_2 79 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 120 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 120 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 251 (accept_3_2 76 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 251 (Polychromatic418967fa.accept_7_5_1_6_1_163
  75 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 120 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 120 251 (accept_3_2 73 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 120 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 120 251 (Polychromatic418967fa.accept_22_5_10_9_1_15147 71 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 251 (accept_3_2 70 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 120 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 251
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 120 251 (accept_3_2 67 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 120 251 (Polychromatic418967fa.accept_13_1_3_4_1_925 66 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 120 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 251 (accept_3_2 64 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 251 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 251
  (Polychromatic418967fa.accept_19_5_6_4_1_8480 62 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 251 (accept_3_2 61 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 120 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 120 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 251 (accept_3_2 58 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 251 (Polychromatic418967fa.accept_22_13_10_9_1_10645 57 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 120 251 (accept_3_2 55 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 120 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 120 251 (Polychromatic418967fa.accept_13_1_3_4_1_925 53 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 251 (accept_3_2 52 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 120 251 (accept_3_2 49 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 120 251 (Polychromatic418967fa.accept_17_14_1_13_1_12898 48 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 251 (accept_3_2 46 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 251 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 120
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 251 (accept_3_2 43 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 120 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 120 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 251 (accept_3_2 40 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 251 (Polychromatic418967fa.accept_21_18_15_20_1_6076 39 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 251 (accept_3_2 37 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 120 251 (Polychromatic418967fa.accept_16_4_8_11_1_5961 36 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 120 251 (Polychromatic418967fa.accept_14_7_8_13_1_3161 35 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 251 (accept_3_2 34 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 251 (accept_3_2 31 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 120 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 120 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 251 (accept_3_2 28 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 251 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 251
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 120 251 (accept_3_2 25 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 120 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 120 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 251 (accept_3_2 22 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 251 (Polychromatic418967fa.accept_14_7_8_13_1_3161 21 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 251 (accept_3_2 19 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 251 (Polychromatic418967fa.accept_21_18_15_20_1_6076 18 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 251 (Polychromatic418967fa.accept_19_17_6_4_1_7027 17 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 251 (accept_3_2 16 120 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 251 (Polychromatic418967fa.accept_9_6_3_8_1_595
  15 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 251 (accept_3_2 13 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 120 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 120 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 251 (accept_3_2 10 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 251
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 251 (accept_3_2 7 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 120 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 251 (accept_3_2 4 120 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 251 (Polychromatic418967fa.accept_16_3_8_11_1_2714 3 120 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 251 (accept_3_2 1 120 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 251 (allA_succ_of_accept 118 119 251 (accept_3_2 118 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 251 (Polychromatic418967fa.accept_15_12_14_11_1_4375 117 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 251 (Polychromatic418967fa.accept_8_4_7_3_1_144
  116 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 251 (accept_3_2
  115 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 251
  (Polychromatic418967fa.accept_9_6_2_8_1_592 114 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 113 119 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 251 (accept_3_2 112 119 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 119 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 111 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 251
  (Polychromatic418967fa.accept_13_6_2_4_1_923 110 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 119 251 (accept_3_2 109 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 119 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 108 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 119 251 (Polychromatic418967fa.accept_19_12_5_4_1_11267 107 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 251 (accept_3_2 106 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 105 119
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 104 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 119 251 (accept_3_2 103 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 119 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 119 251 (Polychromatic418967fa.accept_16_5_7_11_1_2664 101 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 251 (accept_3_2 100 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 251 (Polychromatic418967fa.accept_14_1_7_13_1_333 99 119
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 251
  (Polychromatic418967fa.accept_10_8_9_1_1_189 98 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 119 251 (accept_3_2 97 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 119 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 119 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 251 (accept_3_2 94 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 251
  (Polychromatic418967fa.accept_8_4_7_3_1_144 92 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 251 (accept_3_2 91 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 251 (Polychromatic418967fa.accept_13_12_2_4_1_3131 90 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 251 (Polychromatic418967fa.accept_13_11_2_4_1_1590 89 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 251 (accept_3_2 88 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 119 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 251 (accept_3_2 85 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 251 (Polychromatic418967fa.accept_13_5_2_4_1_3955 83 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 251 (accept_3_2 82 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 251 (Polychromatic418967fa.accept_21_18_14_20_1_9251 81
  119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 251
  (Polychromatic418967fa.accept_21_17_14_20_1_7811 80 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 119 251 (accept_3_2 79 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 119 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 119 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 119 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 251 (accept_3_2 76 119 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 251 (Polychromatic418967fa.accept_9_3_2_8_1_108
  75 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 251
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 74 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 119 251 (accept_3_2 73 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 119 251 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 119 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 251 (Polychromatic418967fa.accept_13_6_2_4_1_923 71 119
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 251 (accept_3_2 70 119
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 251
  (Polychromatic418967fa.accept_9_6_2_8_1_592 69 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 119 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 68 119 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 251 (accept_3_2 67 119 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 119 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 251 (Polychromatic418967fa.accept_10_5_9_1_1_187
  65 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 251 (accept_3_2 64
  119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 251
  (Polychromatic418967fa.accept_13_11_2_4_1_1590 63 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 119 251 (Polychromatic418967fa.accept_10_2_9_1_1_185 62 119 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 251 (accept_3_2 61 119 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 119 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 251 (Polychromatic418967fa.accept_9_5_2_8_1_109
  59 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 251 (accept_3_2 58
  119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 251
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 119 251 (Polychromatic418967fa.accept_18_2_11_17_1_4773 56 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 251 (accept_3_2 55 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 251 (Polychromatic418967fa.accept_25_4_19_1_1_8146 54 119 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 251
  (Polychromatic418967fa.accept_16_5_7_11_1_2664 53 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 251 (accept_3_2 52 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 251 (accept_3_2 49 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 251
  (Polychromatic418967fa.accept_16_15_7_11_1_3760 47 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 119 251 (accept_3_2 46 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 119 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 119 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 119 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 251 (accept_3_2 43 119 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 251 (Polychromatic418967fa.accept_9_6_2_8_1_592
  42 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 251 (accept_3_2 40 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 251 (Polychromatic418967fa.accept_10_8_9_1_1_189 38 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 251 (accept_3_2 37 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 119 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 251
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 251 (accept_3_2 34 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 251 (accept_3_2 31 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 251
  (Polychromatic418967fa.accept_14_1_7_13_1_333 29 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 251 (accept_3_2 28 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 251 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 251 (Polychromatic418967fa.accept_21_5_14_20_1_9265 26 119 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 251 (accept_3_2 25 119 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 251 (Polychromatic418967fa.accept_9_6_2_8_1_592
  24 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 251 (accept_3_2 22 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 251 (accept_3_2 19 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 251 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 251
  (Polychromatic418967fa.accept_21_17_14_20_1_7811 17 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 119 251 (accept_3_2 16 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 119 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 119 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 119 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 251 (accept_3_2 13 119 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 251 (Polychromatic418967fa.accept_8_4_7_3_1_144
  12 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 251
  (Polychromatic418967fa.accept_13_11_2_4_1_1590 11 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 251 (accept_3_2 10 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 251 (Polychromatic418967fa.accept_19_9_5_4_1_1866 9 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 251 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 251 (accept_3_2 7 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 119 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 251 (accept_3_2 4 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 119 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 251 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 251 (accept_3_2 1 119 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 251 (allA_of_3_0 118 118 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 251
  (allA_succ_of_accept 116 117 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 117 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 251 (accept_3_2 115 117 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 117 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 113 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 251 (accept_3_2 112 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 111 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 251 (accept_3_2 109 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 251 (Polychromatic418967fa.accept_19_13_3_4_1_15146 108
  117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 251
  (Polychromatic418967fa.accept_17_5_15_13_1_7936 107 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 117 251 (accept_3_2 106 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 117 251 (Polychromatic418967fa.accept_16_9_5_11_1_3776 105 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 251 (Polychromatic418967fa.accept_6_2_3_5_1_26
  104 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 251 (accept_3_2
  103 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 117 251 (Polychromatic418967fa.accept_11_2_7_9_1_890 101 117 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 251 (accept_3_2 100 117 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 117 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 99 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 98
  117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 251 (accept_3_2 97
  117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 251
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 96 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 117 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 95 117 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 251 (accept_3_2 94 117 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 117 251 (Polychromatic418967fa.accept_11_5_7_9_1_2696 93 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 251 (accept_3_2 91 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 117 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 251 (Polychromatic418967fa.accept_15_14_12_11_1_1572 89 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 251 (accept_3_2 88 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 87 117
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 117 251 (accept_3_2 85 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 117 251 (Polychromatic418967fa.accept_10_4_7_1_1_471 84 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 117 251 (Polychromatic418967fa.accept_15_8_12_11_1_1570 83 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 251 (accept_3_2 82 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 117 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 251 (accept_3_2 79 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 117 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 117 251 (Polychromatic418967fa.accept_19_1_3_4_1_4306 77 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 251 (accept_3_2 76 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 117
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 251 (accept_3_2 73 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 117 251 (Polychromatic418967fa.accept_16_8_5_11_1_4776 72 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 117 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 251 (accept_3_2 70 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 251 (Polychromatic418967fa.accept_18_15_9_17_1_6043 69 117 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 251 (accept_3_2 67 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 117 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 117 251 (Polychromatic418967fa.accept_19_8_3_4_1_9865 65 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 251 (accept_3_2 64 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 117
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 251 (accept_3_2 61 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 117 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 117 251 (Polychromatic418967fa.accept_15_14_12_11_1_1572 59 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 251 (accept_3_2 58 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 117 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 251 (accept_3_2 55 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 117 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 117 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 251 (accept_3_2 52 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 251 (accept_3_2 49 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 117 251 (Polychromatic418967fa.accept_14_6_5_13_1_367 48 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 251 (Polychromatic418967fa.accept_27_20_9_8_1_15145 47 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 251 (accept_3_2 46 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 251 (Polychromatic418967fa.accept_17_11_15_13_1_11717 45
  117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 251 (accept_3_2 43 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 117 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 117 251 (Polychromatic418967fa.accept_16_9_5_11_1_3776 41 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 251 (accept_3_2 40 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 117 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 251 (accept_3_2 37 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 251 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 251 (accept_3_2 34 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 251 (Polychromatic418967fa.accept_18_15_9_17_1_6043 33 117
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 251 (accept_3_2 31 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 251 (accept_3_2 28 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 251 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 251 (accept_3_2 25 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 251 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 251 (Polychromatic418967fa.accept_15_8_12_11_1_1570 23 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 251 (accept_3_2 22 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 251 (Polychromatic418967fa.accept_20_1_17_11_1_8119 21 117
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 251 (accept_3_2 19 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 251 (Polychromatic418967fa.accept_27_17_9_8_1_9550 17 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 251 (accept_3_2 16 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 117 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 251 (accept_3_2 13 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 251 (Polychromatic418967fa.accept_18_12_9_17_1_7428 12 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 251 (accept_3_2 10 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 251 (Polychromatic418967fa.accept_16_9_5_11_1_3776 9 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 251 (accept_3_2 7 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 251 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 251 (accept_3_2 4 117 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 117 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 251 (accept_3_2 1 117 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 251 (allA_succ_of_accept 115 116 251 (accept_3_2 115 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 116 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 114 116 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 116 251 (Polychromatic418967fa.accept_11_3_6_9_1_1378 113 116
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 116 251 (accept_3_2 112 116
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 116 251
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 116 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 110 116 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 116 251 (accept_3_2 109 116 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 116 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 108 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 116 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 107 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 116 251 (accept_3_2 106 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 116 251 (Polychromatic418967fa.accept_16_8_4_11_1_2687 104 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 251 (accept_3_2 103 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 116 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 102 116
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 116 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 101 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 116 251 (accept_3_2 100 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 116 251 (Polychromatic418967fa.accept_12_2_8_11_1_31 98 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 116 251 (accept_3_2 97 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 116 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 116 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 116 251
  (Polychromatic418967fa.accept_8_7_4_3_1_156 95 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 116 251 (accept_3_2 94 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 116 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 92 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 116 251 (accept_3_2 91 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 116 251 (Polychromatic418967fa.accept_19_14_2_4_1_8473 90 116
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 116 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 89 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 116 251 (accept_3_2 88 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 116 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 86 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 116 251 (accept_3_2 85 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 116 251 (Polychromatic418967fa.accept_24_12_20_11_1_15144 84 116 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 116 251
  (Polychromatic418967fa.accept_13_5_12_4_1_449 83 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 116 251 (accept_3_2 82 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 116 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 116 251 (accept_3_2 79 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 116 251 (Polychromatic418967fa.accept_17_10_14_13_1_12880 78 116 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 251
  (Polychromatic418967fa.accept_10_7_6_1_1_486 77 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 116 251 (accept_3_2 76 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 116 251 (Polychromatic418967fa.accept_12_2_8_11_1_31 74 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 116 251 (accept_3_2 73 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 116 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 116 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 251
  (Polychromatic418967fa.accept_8_7_4_3_1_156 71 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 116 251 (accept_3_2 70 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 116 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 251 (accept_3_2 67 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 251 (accept_3_2 64 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 251 (accept_3_2 61 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 251 (Polychromatic418967fa.accept_13_8_12_4_1_4858 60 116
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 251 (accept_3_2 58 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 251 (Polychromatic418967fa.accept_16_8_4_11_1_2687 56 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 251 (accept_3_2 55 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 116 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 251
  (Polychromatic418967fa.accept_30_23_26_11_1_15143 53 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 116 251 (accept_3_2 52 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 116 251 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 116
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 251 (accept_3_2 49 116
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 251
  (Polychromatic418967fa.accept_21_6_11_20_1_10794 48 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 116 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 116 251 (accept_3_2 46 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 116 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 116 251 (accept_3_2 43 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 116 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 116 251 (Polychromatic418967fa.accept_13_2_12_4_1_943 41 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 116 251 (accept_3_2 40 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 116 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 116 251 (accept_3_2 37 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 116 251 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 116 251 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 251 (accept_3_2 34 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 251
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 116 251 (accept_3_2 31 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 116 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 116 251 (Polychromatic418967fa.accept_13_3_12_4_1_110 29 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 251 (accept_3_2 28 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 116 251 (accept_3_2 25 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 116 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 116 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 251 (accept_3_2 22 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 251
  (Polychromatic418967fa.accept_13_7_12_4_1_450 20 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 116 251 (accept_3_2 19 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 251 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 251 (accept_3_2 16 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 251
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 116 251 (accept_3_2 13 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 116 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 116 251 (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 251 (accept_3_2 10 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 251
  (Polychromatic418967fa.accept_13_8_12_4_1_4858 8 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 251 (accept_3_2 7 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 251 (Polychromatic418967fa.accept_16_6_4_11_1_1719 6 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 251 (accept_3_2 4 116 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 251 (accept_3_2 1 116 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 251 (allA_of_3_0 115 115 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 251
  (allA_succ_of_accept 113 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 113 114 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 114 251 (accept_3_2 112 114 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 114 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 111 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 110 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 114 251 (accept_3_2 109 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 114 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 108 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 114 251 (Polychromatic418967fa.accept_10_7_4_1_1_1319 107 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 251 (accept_3_2 106 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 114 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 114 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 104 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 114 251 (accept_3_2 103 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 114 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 102 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 251 (accept_3_2 100 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 114 251
  (Polychromatic418967fa.accept_13_7_10_4_1_919 98 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 114 251 (accept_3_2 97 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 114 251 (Polychromatic418967fa.accept_13_5_10_4_1_1564 96 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 114 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 95 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 251 (accept_3_2 94 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 92 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 114 251 (accept_3_2 91 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 114 251 (Polychromatic418967fa.accept_11_2_4_9_1_484 90 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 251 (accept_3_2 88 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 86 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 114 251 (accept_3_2 85 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 114 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 114 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 251 (accept_3_2 82 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 251
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 114 251 (accept_3_2 79 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 114 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 251 (accept_3_2 76 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 114 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 114 251 (accept_3_2 73 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 114 251 (Polychromatic418967fa.accept_13_7_10_4_1_919 72 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 114 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 251 (accept_3_2 70 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 114 251 (accept_3_2 67 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 114 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 251 (accept_3_2 64 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 114 251 (Polychromatic418967fa.accept_13_11_10_4_1_1565 63 114 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 251
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 62 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 114 251 (accept_3_2 61 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 114 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 114 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 251 (accept_3_2 58 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 114 251 (accept_3_2 55 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 114 251 (Polychromatic418967fa.accept_16_6_2_11_1_7132 54 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 251 (accept_3_2 52 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 251 (Polychromatic418967fa.accept_15_6_9_11_1_858 51 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 114 251 (accept_3_2 49 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 114 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 114 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 251 (accept_3_2 46 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 251
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 44 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 114 251 (accept_3_2 43 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 114 251 (Polychromatic418967fa.accept_22_20_4_9_1_15142 42 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 251 (accept_3_2 40 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 251
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 114 251 (accept_3_2 37 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 114 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 114 251 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 251 (accept_3_2 34 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 114 251 (accept_3_2 31 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 114 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 251 (accept_3_2 28 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 251 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 251
  (Polychromatic418967fa.accept_20_6_14_11_1_6537 26 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 114 251 (accept_3_2 25 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 114 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 114 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 114 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 251 (accept_3_2 22 114 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 114 251 (accept_3_2 19 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 114 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 251 (accept_3_2 16 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 251 (accept_3_2 13 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 114 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 114 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 251 (accept_3_2 10 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 251 (accept_3_2 7 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  114 251 (Polychromatic418967fa.accept_13_6_10_4_1_957 6 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 114 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 251 (accept_3_2 4 114 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 114 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 251 (accept_3_2 1 114 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 251 (allA_succ_of_accept 112 113 251 (accept_3_2 112 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 111 113 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 113
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 251 (accept_3_2 109 113
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 251
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 108 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 107 113 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 251 (accept_3_2 106 113 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 105 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 251
  (Polychromatic418967fa.accept_20_4_13_11_1_12460 104 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 113 251 (accept_3_2 103 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 113 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 113 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 113
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 251 (accept_3_2 100 113
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 251
  (Polychromatic418967fa.accept_13_8_9_4_1_1552 99 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 113 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 113 251 (accept_3_2 97 113 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 113 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 113 251
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 95 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 113 251 (accept_3_2 94 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 113 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 113 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 113 251 (accept_3_2 91 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 113 251
  (Polychromatic418967fa.accept_7_5_1_6_1_163 89 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 113 251 (accept_3_2 88 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 113 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 87 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 113 251 (accept_3_2 85 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 113 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 113 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 113 251 (accept_3_2 82 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 113 251 (Polychromatic418967fa.accept_19_5_18_4_1_2956 81 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 113 251 (Polychromatic418967fa.accept_15_5_8_11_1_2350 80 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 113 251 (accept_3_2 79 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 113 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 251
  (Polychromatic418967fa.accept_14_7_1_13_1_357 77 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 113 251 (accept_3_2 76 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 113 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 251 (accept_3_2 73 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 113 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 251
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 71 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 113 251 (accept_3_2 70 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 113 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 113 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 251 (accept_3_2 67 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 113 251 (accept_3_2 64 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 113 251 (Polychromatic418967fa.accept_14_7_1_13_1_357 63 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 251 (accept_3_2 61 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 251
  (Polychromatic418967fa.accept_13_7_9_4_1_918 59 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 251 (accept_3_2 58 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 251 (accept_3_2 55 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 251
  (Polychromatic418967fa.accept_19_15_18_4_1_9834 53 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 113 251 (accept_3_2 52 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 113 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 113 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 251 (accept_3_2 49 113 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 48
  113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 251
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 251 (accept_3_2 46 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 251 (Polychromatic418967fa.accept_13_6_9_4_1_2288 45 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 251 (accept_3_2 43 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 251
  (Polychromatic418967fa.accept_17_7_11_13_1_2037 41 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 113 251 (accept_3_2 40 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 113 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 113 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 251 (accept_3_2 37 113 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 251
  (Polychromatic418967fa.accept_19_17_18_4_1_12571 36 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 251 (Polychromatic418967fa.accept_14_7_1_13_1_357 35 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 251 (accept_3_2 34 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 113 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 251
  (Polychromatic418967fa.accept_10_2_3_1_1_481 32 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 251 (accept_3_2 31 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 251 (accept_3_2 28 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 251 (Polychromatic418967fa.accept_15_12_8_11_1_4383 27 113 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 251 (accept_3_2 25 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 251 (accept_3_2 22 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 251 (accept_3_2 19 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 251 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 251 (accept_3_2 16 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 113 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 251 (accept_3_2 13 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 251 (accept_3_2 10 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 251
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 251 (accept_3_2 7 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 251 (accept_3_2 4 113 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 113 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 251 (accept_3_2 1 113 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 251 (allA_of_3_0 112 112 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 251
  (allA_succ_of_accept 110 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 111 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 251 (accept_3_2 109 111 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 108 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 251
  (Polychromatic418967fa.accept_13_3_7_4_1_435 107 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 251 (accept_3_2 106 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 251 (accept_3_2 103 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 251 (Polychromatic418967fa.accept_13_11_7_4_1_1561 102
  111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 101 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 251 (accept_3_2 100 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 251 (Polychromatic418967fa.accept_15_9_6_11_1_1586 99 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 251 (accept_3_2 97 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 95 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 251 (accept_3_2 94 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 93 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 251 (accept_3_2 91 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 251 (Polychromatic418967fa.accept_13_12_7_4_1_3124 90 111 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 251
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 89 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 251 (accept_3_2 88 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 251 (accept_3_2 85 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 251 (accept_3_2 82 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 251 (accept_3_2 79 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 251 (accept_3_2 76 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 251 (Polychromatic418967fa.accept_13_10_7_4_1_2262 75 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 251 (accept_3_2 73 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 251 (Polychromatic418967fa.accept_17_4_9_13_1_2020 72 111 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 251
  (Polychromatic418967fa.accept_13_6_7_4_1_2264 71 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 251 (accept_3_2 70 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 251 (accept_3_2 67 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 251 (Polychromatic418967fa.accept_19_9_16_4_1_5584 66 111 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 251 (accept_3_2 64 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 251 (Polychromatic418967fa.accept_13_11_7_4_1_1561 63 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 251 (accept_3_2 61 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 251 (accept_3_2 58 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 251 (accept_3_2 55 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 251 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 111 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 251
  (Polychromatic418967fa.accept_21_11_6_20_1_4589 53 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 111 251 (accept_3_2 52 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 111 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 111 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 111 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 251 (accept_3_2 49 111 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 251 (Polychromatic418967fa.accept_13_9_7_4_1_953
  48 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 251 (accept_3_2 46 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 251 (accept_3_2 43 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 251 (accept_3_2 40 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 251 (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 251 (accept_3_2 37 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 251
  (Polychromatic418967fa.accept_13_9_7_4_1_953 35 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 251 (accept_3_2 34 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 251 (accept_3_2 31 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 251 (Polychromatic418967fa.accept_19_11_16_4_1_7075 30 111 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 251 (accept_3_2 28 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 251 (Polychromatic418967fa.accept_17_10_9_13_1_6644 27 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 251 (accept_3_2 25 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 251 (accept_3_2 22 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 251 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 251 (accept_3_2 19 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 251 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 251
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 251 (accept_3_2 16 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 251 (accept_3_2 13 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 251 (accept_3_2 10 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 251 (accept_3_2 7 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 111 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 251 (accept_3_2 4 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 251 (Polychromatic418967fa.accept_13_3_7_4_1_435 3 111 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 251 (accept_3_2 1 111 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 251 (allA_succ_of_accept 109 110 251 (accept_3_2 109 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 251 (Polychromatic418967fa.accept_19_13_15_4_1_5614 108 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 251
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 107 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 110 251 (accept_3_2 106 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 110 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 110 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 110
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 110 251 (accept_3_2 103 110
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 110 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 102 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 110 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 110 251 (accept_3_2 100 110 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 110 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 110 251 (Polychromatic418967fa.accept_13_7_6_4_1_933
  98 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 110 251 (accept_3_2 97
  110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 110 251
  (Polychromatic418967fa.accept_9_6_2_8_1_592 96 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 110 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 95 110 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 110 251 (accept_3_2 94 110 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 110 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 92
  110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 251 (accept_3_2 91
  110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 110 251
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 90 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 110 251 (accept_3_2 88 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 110 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 110 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 110 251 (accept_3_2 85 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 110 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 110 251 (Polychromatic418967fa.accept_13_5_6_4_1_1582 83 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 110 251 (accept_3_2 82 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 110 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 110 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 110 251 (accept_3_2 79 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 110 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 110 251 (accept_3_2 76 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 110 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 110 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 74 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 110 251 (accept_3_2 73 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 110 251 (Polychromatic418967fa.accept_13_7_6_4_1_933 72 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 110 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 110 251 (accept_3_2 70 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 110 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 110 251 (accept_3_2 67 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 110 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 110 251 (accept_3_2 64 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 110 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 251
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 62 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 110 251 (accept_3_2 61 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 110 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 110 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 110 251 (accept_3_2 58 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 110 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 110 251 (accept_3_2 55 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 110 251 (Polychromatic418967fa.accept_13_2_6_4_1_1593 54 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 251 (accept_3_2 52 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 110 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 110 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 110 251 (accept_3_2 49 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 110 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 110 251 (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 110 251 (accept_3_2 46 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 110 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 110 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 110 251 (accept_3_2 43 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 110 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 110 251 (accept_3_2 40 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 110 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 251
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 38 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 110 251 (accept_3_2 37 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 110 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 110 251 (Polychromatic418967fa.accept_13_9_6_4_1_2243 35 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 251 (accept_3_2 34 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 110 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 251 (accept_3_2 31 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 110 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 251 (accept_3_2 28 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 251
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 110 251 (accept_3_2 25 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 110 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 110 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 251 (accept_3_2 22 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 110 251 (accept_3_2 19 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 110 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 251 (accept_3_2 16 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 110 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 110 251 (accept_3_2 13 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 110 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 110 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 251 (accept_3_2 10 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 251 (accept_3_2 7 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 251 (accept_3_2 4 110 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 110 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 251
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 2 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 251 (accept_3_2 1 110 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 251 (allA_of_3_0 109 109 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 251
  (allA_succ_of_accept 107 108 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 107 108 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 251 (accept_3_2 106 108 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 108 251 (Polychromatic418967fa.accept_19_10_13_4_1_5583 105 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 251
  (Polychromatic418967fa.accept_15_14_3_11_1_850 104 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 108 251 (accept_3_2 103 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 108 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 102 108 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 251 (Polychromatic418967fa.accept_14_3_10_13_1_339 101
  108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 251 (accept_3_2 100
  108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 251
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 99 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 108 251 (Polychromatic418967fa.accept_15_8_3_11_1_849 98 108 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 108 251 (accept_3_2 97 108 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 108 251 (Polychromatic418967fa.accept_15_6_3_11_1_848 96 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 108 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 95 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 108 251 (accept_3_2 94 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 108 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 108 251 (Polychromatic418967fa.accept_17_7_6_13_1_10548 92 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 108 251 (accept_3_2 91 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 108 251 (Polychromatic418967fa.accept_16_10_12_11_1_346 90 108
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 108 251
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 89 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 108 251 (accept_3_2 88 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 108 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 87 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 108 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 108 251 (accept_3_2 85 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 108 251 (Polychromatic418967fa.accept_16_4_12_11_1_2650 84 108 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 251
  (Polychromatic418967fa.accept_10_3_8_1_1_182 83 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 108 251 (accept_3_2 82 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 108 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 108 251 (Polychromatic418967fa.accept_21_17_3_20_1_6054 80 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 108 251 (accept_3_2 79 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 108 251 (Polychromatic418967fa.accept_20_18_8_11_1_9699 78 108
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 251
  (Polychromatic418967fa.accept_20_17_8_11_1_6615 77 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 108 251 (accept_3_2 76 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 108 251 (Polychromatic418967fa.accept_17_7_6_13_1_10548 75 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 251 (Polychromatic418967fa.accept_7_4_3_6_1_340
  74 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 251 (accept_3_2 73
  108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 108 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 108 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 71 108 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 251 (accept_3_2 70 108 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 108 251 (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 251
  (Polychromatic418967fa.accept_15_8_3_11_1_849 68 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 108 251 (accept_3_2 67 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 108 251 (Polychromatic418967fa.accept_15_6_3_11_1_848 66 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 108 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 251 (accept_3_2 64 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 251
  (Polychromatic418967fa.accept_17_11_6_13_1_10553 62 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 108 251 (accept_3_2 61 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 108 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 108 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 108 251 (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 108
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 251 (accept_3_2 58 108
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 251
  (Polychromatic418967fa.accept_20_17_8_11_1_6615 57 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 108 251 (Polychromatic418967fa.accept_16_8_12_11_1_3697 56 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 251 (accept_3_2 55 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 251 (Polychromatic418967fa.accept_21_12_3_20_1_4567 54 108
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 108 251 (accept_3_2 52 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 108 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 108 251 (Polychromatic418967fa.accept_22_6_20_9_1_9031 50 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 251 (accept_3_2 49 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 251 (Polychromatic418967fa.accept_19_10_13_4_1_5583 48 108
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 251
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 108 251 (accept_3_2 46 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 108 251 (Polychromatic418967fa.accept_14_3_10_13_1_339 45 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 108 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 251 (accept_3_2 43 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 251 (Polychromatic418967fa.accept_16_10_12_11_1_346 42 108 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 251
  (Polychromatic418967fa.accept_17_7_6_13_1_10548 41 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 108 251 (accept_3_2 40 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 108 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 108 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 251 (Polychromatic418967fa.accept_15_8_3_11_1_849 38 108
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 251 (accept_3_2 37 108
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 251
  (Polychromatic418967fa.accept_15_6_3_11_1_848 36 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 108 251 (Polychromatic418967fa.accept_43_35_22_36_1_15141 35 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 251 (accept_3_2 34 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 251 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 108 251 (accept_3_2 31 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 108 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 108 251 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 251 (accept_3_2 28 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 251 (Polychromatic418967fa.accept_19_8_13_4_1_15140 27 108
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 251
  (Polychromatic418967fa.accept_16_10_12_11_1_346 26 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 108 251 (accept_3_2 25 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 108 251 (Polychromatic418967fa.accept_16_8_12_11_1_3697 24 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 23
  108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 251 (accept_3_2 22
  108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 251
  (Polychromatic418967fa.accept_15_6_3_11_1_848 21 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 251 (Polychromatic418967fa.accept_16_4_12_11_1_2650 20 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 251 (accept_3_2 19 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 251
  (Polychromatic418967fa.accept_14_3_10_13_1_339 17 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 251 (accept_3_2 16 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 108 251 (Polychromatic418967fa.accept_15_14_3_11_1_850 14 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 251 (accept_3_2 13 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 251 (Polychromatic418967fa.accept_21_12_3_20_1_4567 12 108
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 251 (accept_3_2 10 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  108 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 108 251 (Polychromatic418967fa.accept_15_8_3_11_1_849 8 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 251 (accept_3_2 7 108 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 251 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 108 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 251
  (Polychromatic418967fa.accept_23_5_16_21_1_15139 5 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 108 251 (accept_3_2 4 108 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 108 251 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 108 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 108 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 251 (accept_3_2 1 108 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 251 (allA_succ_of_accept 106 107 251 (accept_3_2 106 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 251 (Polychromatic418967fa.accept_13_1_3_4_1_925 105 107 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 251 (Polychromatic418967fa.accept_10_4_7_1_1_471 104 107
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 251 (accept_3_2 103 107
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 102 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 101 107 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 251 (accept_3_2 100 107 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 251 (Polychromatic418967fa.accept_11_10_8_9_1_492
  98 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 251 (accept_3_2 97
  107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 251
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 96 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 107 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 95 107 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 251 (accept_3_2 94 107 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 107 251 (Polychromatic418967fa.accept_17_8_5_13_1_4158 93 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 92 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 251 (accept_3_2 91 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 251 (Polychromatic418967fa.accept_13_12_3_4_1_928 90 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 251 (Polychromatic418967fa.accept_21_5_2_20_1_6081 89 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 251 (accept_3_2 88 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 107 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 251
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 86 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 251 (accept_3_2 85 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 251 (Polychromatic418967fa.accept_10_4_7_1_1_471 84 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 251 (Polychromatic418967fa.accept_17_15_5_13_1_6626 83 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 251 (accept_3_2 82 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 107 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 251
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 251 (accept_3_2 79 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 251 (Polychromatic418967fa.accept_13_12_3_4_1_928 77 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 251 (accept_3_2 76 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 251 (Polychromatic418967fa.accept_23_6_15_21_1_3566 75 107
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 251 (accept_3_2 73 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 251 (Polychromatic418967fa.accept_13_7_3_4_1_459 72 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 251 (accept_3_2 70 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 251 (Polychromatic418967fa.accept_15_9_2_11_1_2391 69 107 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 251
  (Polychromatic418967fa.accept_19_11_12_4_1_8455 68 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 107 251 (accept_3_2 67 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 107 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 107 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 251 (Polychromatic418967fa.accept_11_10_8_9_1_492 65 107
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 251 (accept_3_2 64 107
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 251
  (Polychromatic418967fa.accept_19_6_12_4_1_8516 63 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 107 251 (Polychromatic418967fa.accept_19_5_12_4_1_8467 62 107 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 251 (accept_3_2 61 107 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 107 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 59
  107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 251 (accept_3_2 58
  107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 107 251 (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 107 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 251 (accept_3_2 55 107 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 107 251 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 251 (accept_3_2 52 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 251 (Polychromatic418967fa.accept_13_12_3_4_1_928 51 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 251 (accept_3_2 49 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 251 (Polychromatic418967fa.accept_21_6_2_20_1_7803 48 107 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 251
  (Polychromatic418967fa.accept_21_5_2_20_1_6081 47 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 251 (accept_3_2 46 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 251 (Polychromatic418967fa.accept_10_4_7_1_1_471 44 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 251 (accept_3_2 43 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 251 (Polychromatic418967fa.accept_17_8_5_13_1_4158 42 107
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 251
  (Polychromatic418967fa.accept_20_1_7_11_1_3673 41 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 251 (accept_3_2 40 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 251 (accept_3_2 37 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 251
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 251 (accept_3_2 34 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 251 (Polychromatic418967fa.accept_13_7_3_4_1_459 33 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 251 (accept_3_2 31 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 251 (Polychromatic418967fa.accept_19_11_12_4_1_8455 30 107 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 251 (accept_3_2 28 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 251 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 251 (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 251 (accept_3_2 25 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 107 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 251
  (Polychromatic418967fa.accept_25_23_7_1_1_9892 23 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 251 (accept_3_2 22 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 251 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 251 (Polychromatic418967fa.accept_13_7_3_4_1_459 20 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 251 (accept_3_2 19 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 107 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 251
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 251 (accept_3_2 16 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 251 (Polychromatic418967fa.accept_10_4_7_1_1_471 14 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 251 (accept_3_2 13 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 251 (Polychromatic418967fa.accept_13_12_3_4_1_928 12 107
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 251 (accept_3_2 10 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 251 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 251 (accept_3_2 7 107 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 251 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 251
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 251 (accept_3_2 4 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 107 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 251 (Polychromatic418967fa.accept_19_2_12_4_1_4193 2 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 251 (accept_3_2 1 107 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 107
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 251 (allA_of_3_0 106 106 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 251
  (allA_succ_of_accept 104 105 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 105 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 251 (accept_3_2 103 105 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 251 (accept_3_2 100 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 251 (Polychromatic418967fa.accept_10_9_5_1_1_1325 99 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 251 (accept_3_2 97 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 251 (Polychromatic418967fa.accept_10_6_5_1_1_482 96 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 251 (accept_3_2 94 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 251 (accept_3_2 91 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 251
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 89 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 251 (accept_3_2 88 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 87 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 251 (accept_3_2 85 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 251 (accept_3_2 82 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 251 (Polychromatic418967fa.accept_13_3_1_4_1_945 81 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 251 (accept_3_2 79 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 251 (accept_3_2 76 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 251 (accept_3_2 73 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 251 (Polychromatic418967fa.accept_17_4_3_13_1_6692 72 105 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 251
  (Polychromatic418967fa.accept_14_1_7_13_1_333 71 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 251 (accept_3_2 70 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 251 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 251 (accept_3_2 67 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 251 (accept_3_2 64 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 251 (accept_3_2 61 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 251 (Polychromatic418967fa.accept_18_6_15_17_1_7363 60 105 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 251 (accept_3_2 58 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 251 (accept_3_2 55 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 251
  (Polychromatic418967fa.accept_16_5_9_11_1_3762 53 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 251 (accept_3_2 52 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 251 (accept_3_2 49 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 251 (accept_3_2 46 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 251 (Polychromatic418967fa.accept_18_9_15_17_1_3497 45 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 251 (accept_3_2 43 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 251 (accept_3_2 40 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 251 (accept_3_2 37 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 251 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 251
  (Polychromatic418967fa.accept_19_16_10_4_1_9855 35 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 105 251 (accept_3_2 34 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 105 251 (Polychromatic418967fa.accept_17_16_3_13_1_2052 33 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 32
  105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 251 (accept_3_2 31
  105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 105 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 251 (accept_3_2 28 105 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 251 (accept_3_2 25 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 251 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 251 (accept_3_2 22 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 251 (accept_3_2 19 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 251 (Polychromatic418967fa.accept_19_17_10_4_1_7032 17 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 251 (accept_3_2 16 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 105
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 251 (accept_3_2 13 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 251 (accept_3_2 10 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 251 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 251 (accept_3_2 7 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 251 (accept_3_2 4 105 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 105 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 251 (accept_3_2 1 105 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 251 (allA_succ_of_accept 103 104 251 (accept_3_2 103 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 104 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 104
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 251 (accept_3_2 100 104
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 251
  (Polychromatic418967fa.accept_6_3_2_5_1_32 99 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 251 (Polychromatic418967fa.accept_12_2_8_11_1_31 98 104 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 251 (accept_3_2 97 104 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 251 (Polychromatic418967fa.accept_10_5_4_1_1_842
  95 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 104 251 (accept_3_2 94
  104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 104 251
  (Polychromatic418967fa.accept_6_3_2_5_1_32 93 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 104 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 104 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 251 (accept_3_2 91 104 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 104 251 (Polychromatic418967fa.accept_19_14_9_4_1_7029 90 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 251
  (Polychromatic418967fa.accept_14_5_6_13_1_3145 89 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 104 251 (accept_3_2 88 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 104 251 (Polychromatic418967fa.accept_12_2_8_11_1_31 86 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 251 (accept_3_2 85 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 104 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 251 (accept_3_2 82 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 251 (Polychromatic418967fa.accept_25_5_4_1_1_15138 80 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 251 (accept_3_2 79 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 104 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 251
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 77 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 104 251 (accept_3_2 76 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 104 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 251 (accept_3_2 73 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 251 (Polychromatic418967fa.accept_15_12_14_11_1_4375 72 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 251
  (Polychromatic418967fa.accept_19_14_9_4_1_7029 71 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 251 (accept_3_2 70 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 251 (Polychromatic418967fa.accept_14_12_6_13_1_3173 68 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 251 (accept_3_2 67 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 251 (accept_3_2 64 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 251 (Polychromatic418967fa.accept_11_7_5_9_1_884 62 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 251 (accept_3_2 61 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 251
  (Polychromatic418967fa.accept_19_2_9_4_1_2951 59 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 104 251 (accept_3_2 58 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 104 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 251 (accept_3_2 55 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 251 (Polychromatic418967fa.accept_14_12_6_13_1_3173 54 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 251
  (Polychromatic418967fa.accept_16_5_8_11_1_9582 53 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 104 251 (accept_3_2 52 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 104 251 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 251 (accept_3_2 49 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 251 (accept_3_2 46 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 251 (Polychromatic418967fa.accept_16_12_8_11_1_2695 44 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 251 (accept_3_2 43 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 251
  (Polychromatic418967fa.accept_17_7_2_13_1_5397 41 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 251 (accept_3_2 40 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 104 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 251 (accept_3_2 37 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 251 (Polychromatic418967fa.accept_16_4_8_11_1_5961 36 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 251
  (Polychromatic418967fa.accept_10_5_4_1_1_842 35 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 251 (accept_3_2 34 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 251 (Polychromatic418967fa.accept_17_15_2_13_1_4153 32 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 251 (accept_3_2 31 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 251 (accept_3_2 28 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 251 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 251 (accept_3_2 25 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 251
  (Polychromatic418967fa.accept_17_6_2_13_1_3051 23 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 251 (accept_3_2 22 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 251 (accept_3_2 19 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 251 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 251
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 251 (accept_3_2 16 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 251 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 251 (accept_3_2 13 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 104 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 251 (accept_3_2 10 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 251 (Polychromatic418967fa.accept_19_8_9_4_1_5593 8 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 251 (accept_3_2 7 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 104 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 251
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 251 (accept_3_2 4 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 251 (accept_3_2 1 104 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 251 (allA_of_3_0 103 103 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 251 (allA_succ_of_accept 101
  102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 102 251 (accept_3_2 100 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 102 251 (Polychromatic418967fa.accept_10_9_2_1_1_840 99 102 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 251 (Polychromatic418967fa.accept_13_7_11_4_1_2247 98 102
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 251 (accept_3_2 97 102
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 96 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 102 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 102 251 (accept_3_2 94 102 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 251 (Polychromatic418967fa.accept_9_2_3_8_1_318
  92 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 251 (accept_3_2 91
  102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 251
  (Polychromatic418967fa.accept_13_12_11_4_1_3111 90 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 102 251 (accept_3_2 88 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 102 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 86 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 102 251 (accept_3_2 85 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 102 251 (Polychromatic418967fa.accept_13_6_11_4_1_938 84 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 102 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 251 (accept_3_2 82 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 80 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 102 251 (accept_3_2 79 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 102 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 251 (accept_3_2 76 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 102 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 102 251 (accept_3_2 73 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 102 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 102 251 (Polychromatic418967fa.accept_13_6_11_4_1_938 71 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 251 (accept_3_2 70 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 102 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 102 251 (accept_3_2 67 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 102 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 251 (accept_3_2 64 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 102 251 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 251
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 62 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 102 251 (accept_3_2 61 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 102 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 102 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 102 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 102 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 251 (accept_3_2 58 102 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 102 251 (accept_3_2 55 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 102 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 251 (accept_3_2 52 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 251 (accept_3_2 49 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 102 251 (Polychromatic418967fa.accept_21_6_18_20_1_6065 48 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 251 (accept_3_2 46 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 251 (accept_3_2 43 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 102 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 251 (accept_3_2 40 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 251 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 251 (accept_3_2 37 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 102 251 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 102 251 (Polychromatic418967fa.accept_16_3_6_11_1_2718 35 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 251 (accept_3_2 34 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 251 (accept_3_2 31 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 102 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 251 (accept_3_2 28 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 251 (Polychromatic418967fa.accept_18_9_12_17_1_6060 27 102 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 102 251 (accept_3_2 25 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 102 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 102 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 251 (accept_3_2 22 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 251 (accept_3_2 19 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 102 251 (Polychromatic418967fa.accept_16_2_6_11_1_1722 18 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 251 (accept_3_2 16 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 251 (accept_3_2 13 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 102 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 251 (accept_3_2 10 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 251
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 8 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 251 (accept_3_2 7 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  102 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 102 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 251 (accept_3_2 4 102 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 102 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 251 (accept_3_2 1 102 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 251 (allA_succ_of_accept 100 101 251 (accept_3_2 100 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 251 (Polychromatic418967fa.accept_13_8_10_4_1_2270 99 101 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 251 (accept_3_2 97 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 251 (Polychromatic418967fa.accept_9_6_2_8_1_592
  96 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 95 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 251 (accept_3_2 94 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 251 (Polychromatic418967fa.accept_11_4_2_9_1_496 92 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 251 (accept_3_2 91 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 251
  (Polychromatic418967fa.accept_13_11_10_4_1_1565 89 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 101 251 (accept_3_2 88 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 101 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 101 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 251 (accept_3_2 85 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 251 (Polychromatic418967fa.accept_9_3_2_8_1_108
  84 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 251
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 83 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 251 (accept_3_2 82 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 251 (Polychromatic418967fa.accept_14_10_3_13_1_1530 80 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 251 (accept_3_2 79 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 251 (accept_3_2 76 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 251 (accept_3_2 73 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 251
  (Polychromatic418967fa.accept_13_6_10_4_1_957 71 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 251 (accept_3_2 70 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 251 (accept_3_2 67 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 251 (accept_3_2 64 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 251 (Polychromatic418967fa.accept_13_11_10_4_1_1565 63 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 251 (accept_3_2 61 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 251 (accept_3_2 58 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 251 (Polychromatic418967fa.accept_16_8_5_11_1_4776 56 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 251 (accept_3_2 55 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 251 (accept_3_2 52 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 251 (accept_3_2 49 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 251
  (Polychromatic418967fa.accept_13_8_10_4_1_2270 47 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 251 (accept_3_2 46 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 251 (Polychromatic418967fa.accept_13_6_10_4_1_957 45 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 251 (accept_3_2 43 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 251 (accept_3_2 40 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 251 (accept_3_2 37 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 251 (Polychromatic418967fa.accept_19_17_6_4_1_7027 36 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 251
  (Polychromatic418967fa.accept_21_14_17_20_1_12259 35 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 101 251 (accept_3_2 34 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 101 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 101 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 251 (accept_3_2 31 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 251
  (Polychromatic418967fa.accept_11_7_2_9_1_480 29 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 251 (accept_3_2 28 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 251 (Polychromatic418967fa.accept_13_1_10_4_1_954 27 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 251 (accept_3_2 25 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 251 (accept_3_2 22 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 251 (Polychromatic418967fa.accept_13_7_10_4_1_919 20 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 251 (accept_3_2 19 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 251
  (Polychromatic418967fa.accept_19_17_6_4_1_7027 17 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 251 (accept_3_2 16 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 251 (accept_3_2 13 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 101 251 (accept_3_2 10 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  101 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 101 251 (Polychromatic418967fa.accept_13_8_10_4_1_2270 8 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 251 (accept_3_2 7 101 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 251 (accept_3_2 4 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 101 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 251 (accept_3_2 1 101 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 251 (allA_of_3_0 100 100 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 251 (allA_succ_of_accept 98 99
  251 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 251 (accept_3_2 97 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96
  99 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 99 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 95 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 251 (accept_3_2 94 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 251 (accept_3_2 91 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 251 (Polychromatic418967fa.accept_13_12_8_4_1_3099 90 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 251 (accept_3_2 88 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 251 (Polychromatic418967fa.accept_13_9_8_4_1_937 87 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 251 (accept_3_2 85 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 251 (Polychromatic418967fa.accept_18_12_9_17_1_7428 84 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 251 (Polychromatic418967fa.accept_22_17_11_9_1_10636 83 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 251 (accept_3_2 82 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 99
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 251 (accept_3_2 79 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 251 (Polychromatic418967fa.accept_10_8_9_1_1_189 78 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 251 (Polychromatic418967fa.accept_13_12_8_4_1_3099 77 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 251 (accept_3_2 76 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 99 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 251 (accept_3_2 73 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 251 (Polychromatic418967fa.accept_16_7_3_11_1_3682 71 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 251 (accept_3_2 70 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 99
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 251 (accept_3_2 67 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 251 (Polychromatic418967fa.accept_15_6_9_11_1_858 66 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 251 (accept_3_2 64 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 251 (Polychromatic418967fa.accept_13_11_8_4_1_3950 63 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 251 (accept_3_2 61 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 251 (Polychromatic418967fa.accept_21_18_15_20_1_6076 60 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 251 (Polychromatic418967fa.accept_25_9_24_1_1_9923 59 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 251 (accept_3_2 58 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 99
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 251 (accept_3_2 55 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 251 (Polychromatic418967fa.accept_27_26_18_8_1_5412 53 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 251 (accept_3_2 52 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 99 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 251 (accept_3_2 49 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 251 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 251 (accept_3_2 46 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 251 (accept_3_2 43 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 251 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 251 (Polychromatic418967fa.accept_22_19_11_9_1_9028 41 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 251 (accept_3_2 40 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 251 (Polychromatic418967fa.accept_16_7_3_11_1_3682 39 99
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 251 (accept_3_2 37 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 251 (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 251 (accept_3_2 34 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 251 (accept_3_2 31 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 251 (Polychromatic418967fa.accept_31_29_6_3_1_15137 29 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 251 (accept_3_2 28 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 251 (Polychromatic418967fa.accept_17_10_14_13_1_12880 27 99
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 251 (accept_3_2 25 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 251 (Polychromatic418967fa.accept_13_11_8_4_1_3950 24 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 251 (accept_3_2 22 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 251 (accept_3_2 19 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 251 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 251 (Polychromatic418967fa.accept_15_2_9_11_1_1551 17 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 251 (accept_3_2 16 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 99 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 251 (accept_3_2 13 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 251 (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 251 (accept_3_2 10 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 99 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 251 (accept_3_2 7 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  251 (Polychromatic418967fa.accept_15_6_9_11_1_858 6 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 99 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 251 (accept_3_2 4 99 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 251 (Polychromatic418967fa.accept_22_3_11_9_1_12102 3 99 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 251 (accept_3_2 1 99 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  251 (allA_succ_of_accept 97 98 251 (accept_3_2 97 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 251 (Polychromatic418967fa.accept_11_8_10_9_1_1401 96 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 251 (Polychromatic418967fa.accept_15_5_8_11_1_2350 95 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 251 (accept_3_2 94 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 98 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 92 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 251 (accept_3_2 91 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 251 (Polychromatic418967fa.accept_13_12_7_4_1_3124 90 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 251 (accept_3_2 88 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 251
  (Polychromatic418967fa.accept_16_6_2_11_1_7132 86 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 251 (accept_3_2 85 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 251 (Polychromatic418967fa.accept_13_6_7_4_1_2264 84 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 251 (Polychromatic418967fa.accept_10_3_8_1_1_182 83 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 251 (accept_3_2 82 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 251 (accept_3_2 79 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 251 (Polychromatic418967fa.accept_11_1_10_9_1_871 78 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 251 (accept_3_2 76 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 251
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 74 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 251 (accept_3_2 73 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 251 (Polychromatic418967fa.accept_15_12_8_11_1_4383 72 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 251 (Polychromatic418967fa.accept_13_6_7_4_1_2264 71 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 251 (accept_3_2 70 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 251 (accept_3_2 67 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 251 (Polychromatic418967fa.accept_24_18_2_11_1_11843 66 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 251 (accept_3_2 64 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 251
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 62 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 251 (accept_3_2 61 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 251 (Polychromatic418967fa.accept_21_18_14_20_1_9251 60 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 251 (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 251 (accept_3_2 58 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 251
  (Polychromatic418967fa.accept_11_1_10_9_1_871 56 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 251 (accept_3_2 55 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 251 (Polychromatic418967fa.accept_16_6_2_11_1_7132 54 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 251 (accept_3_2 52 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 251
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 50 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 251 (accept_3_2 49 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 251 (Polychromatic418967fa.accept_13_9_7_4_1_953 48 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 251 (Polychromatic418967fa.accept_20_7_18_11_1_5080 47 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 251 (accept_3_2 46 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 251 (accept_3_2 43 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 251 (Polychromatic418967fa.accept_13_3_7_4_1_435 42 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 251 (accept_3_2 40 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 251
  (Polychromatic418967fa.accept_13_12_7_4_1_3124 38 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 251 (accept_3_2 37 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 251 (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 251 (Polychromatic418967fa.accept_13_9_7_4_1_953 35 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 251 (accept_3_2 34 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 251 (accept_3_2 31 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 251 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 251 (accept_3_2 28 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 251
  (Polychromatic418967fa.accept_19_7_3_4_1_13881 26 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 251 (accept_3_2 25 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 251 (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 251 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 251 (accept_3_2 22 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 251 (accept_3_2 19 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 251 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 251 (accept_3_2 16 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 251
  (Polychromatic418967fa.accept_23_14_6_21_1_15136 14 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 98 251 (accept_3_2 13 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 98 251 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 98 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 251 (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 98
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 251 (accept_3_2 10 98 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 251
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 251 (accept_3_2 7 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  251 (Polychromatic418967fa.accept_13_6_7_4_1_2264 6 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 98 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 251 (accept_3_2 4 98 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 98 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 251
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 2 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 98 251 (accept_3_2 1 98 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  251 (allA_of_3_0 97 97 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 251 (allA_succ_of_accept 95 96 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 95 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 96 251 (accept_3_2 94 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  96 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 96 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 92 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 251 (accept_3_2 91 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 251 (Polychromatic418967fa.accept_13_12_5_4_1_3133 90 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 96 251
  (Polychromatic418967fa.accept_22_1_8_9_1_15135 89 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 251 (accept_3_2 88 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  96 251 (Polychromatic418967fa.accept_10_7_6_1_1_486 87 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 96 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 251 (accept_3_2 85 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 96 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 251 (accept_3_2 82 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  96 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 96 251 (Polychromatic418967fa.accept_13_2_5_4_1_3926 80 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 251 (accept_3_2 79 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 96 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 251 (accept_3_2 76 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  96 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 96 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 251 (accept_3_2 73 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 96 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 251 (accept_3_2 70 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  96 251 (Polychromatic418967fa.accept_15_9_6_11_1_1586 69 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 96 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 251 (accept_3_2 67 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 251 (accept_3_2 64 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  96 251 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 96 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 251 (accept_3_2 61 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 251 (accept_3_2 58 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  96 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 96 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 251 (accept_3_2 55 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 251 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 96 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 251 (accept_3_2 52 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  96 251 (Polychromatic418967fa.accept_13_12_5_4_1_3133 51 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 96 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 251 (accept_3_2 49 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 96 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 251 (accept_3_2 46 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  96 251 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 96 251 (Polychromatic418967fa.accept_27_17_15_8_1_15134 44 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 251 (accept_3_2 43 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 96 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 251 (accept_3_2 40 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  96 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 96 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 251 (accept_3_2 37 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 251
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 251 (accept_3_2 34 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 251 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 251 (accept_3_2 31 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 251 (accept_3_2 28 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 251 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 251 (Polychromatic418967fa.accept_19_7_1_4_1_12606 26 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 251 (accept_3_2 25 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 251 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 96
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 251 (accept_3_2 22 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 251 (accept_3_2 19 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 251
  (Polychromatic418967fa.accept_10_7_6_1_1_486 17 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 251 (accept_3_2 16 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 251 (accept_3_2 13 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 251 (accept_3_2 10 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 251 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 251 (accept_3_2 7 96 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 251 (Polychromatic418967fa.accept_13_6_5_4_1_3924 6 96 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 251 (accept_3_2 4 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 96 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 251 (accept_3_2 1 96 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 251
  (allA_succ_of_accept 94 95 251 (accept_3_2 94 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 92 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 251 (accept_3_2 91 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 251 (Polychromatic418967fa.accept_11_2_7_9_1_890 90 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 89 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 251 (accept_3_2 88 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 86 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 251 (accept_3_2 85 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 251 (accept_3_2 82 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 251 (Polychromatic418967fa.accept_15_6_5_11_1_2378 81 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 251 (accept_3_2 79 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 251
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 77 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 251 (accept_3_2 76 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 251 (accept_3_2 73 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 251
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 71 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 251 (accept_3_2 70 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 251 (accept_3_2 67 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 251 (accept_3_2 64 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 251 (Polychromatic418967fa.accept_24_15_23_11_1_11839 63 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 251 (Polychromatic418967fa.accept_15_2_5_11_1_1563 62 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 251 (accept_3_2 61 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 95 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 251 (accept_3_2 58 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 251 (accept_3_2 55 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 251
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 53 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 251 (accept_3_2 52 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 251 (Polychromatic418967fa.accept_20_10_15_11_1_3759 50 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 251 (accept_3_2 49 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 95 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 251 (accept_3_2 46 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 251 (accept_3_2 43 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 251
  (Polychromatic418967fa.accept_23_18_3_21_1_11949 41 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 95 251 (accept_3_2 40 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 95 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 95 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 95 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 251 (accept_3_2 37 95 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 36
  95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 251
  (Polychromatic418967fa.accept_11_2_7_9_1_890 35 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 251 (accept_3_2 34 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 251 (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 251 (accept_3_2 31 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 95 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 251 (accept_3_2 28 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 251 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 251 (accept_3_2 25 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 251 (accept_3_2 22 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 251 (accept_3_2 19 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 251 (Polychromatic418967fa.accept_21_18_11_20_1_3154 18 95 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 251 (accept_3_2 16 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 251 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 251 (accept_3_2 13 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 251 (accept_3_2 10 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 251 (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 251 (accept_3_2 7 95 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 95 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 251 (accept_3_2 4 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  251 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 95 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 95 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 251 (accept_3_2 1 95 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 251
  (allA_of_3_0 94 94 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 251 (allA_succ_of_accept 92 93 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 251 (accept_3_2 91 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 251 (Polychromatic418967fa.accept_13_11_2_4_1_1590 89 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 251 (accept_3_2 88 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 93 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 251 (accept_3_2 85 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 251 (Polychromatic418967fa.accept_11_7_5_9_1_884 84 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 251 (accept_3_2 82 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 251 (accept_3_2 79 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 251 (accept_3_2 76 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 251 (accept_3_2 73 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 251 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 251 (accept_3_2 70 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 251 (accept_3_2 67 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 251 (accept_3_2 64 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 251 (accept_3_2 61 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 251 (accept_3_2 58 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 251 (accept_3_2 55 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 251 (accept_3_2 52 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 251 (accept_3_2 49 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 251 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 251 (accept_3_2 46 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 251 (accept_3_2 43 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 251 (accept_3_2 40 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 251 (accept_3_2 37 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 251 (Polychromatic418967fa.accept_20_15_13_11_1_5110 35 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 251 (accept_3_2 34 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 93 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 251 (accept_3_2 31 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 251 (accept_3_2 28 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 251 (accept_3_2 25 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 251 (accept_3_2 22 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 251 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 251 (accept_3_2 19 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 251 (accept_3_2 16 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 251 (accept_3_2 13 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 251 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 251 (accept_3_2 10 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 251 (Polychromatic418967fa.accept_27_9_12_8_1_15133 9 93 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 251 (accept_3_2 7 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 93 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 251 (accept_3_2 4 93 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 93 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 251 (accept_3_2 1 93 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 251
  (allA_succ_of_accept 91 92 251 (accept_3_2 91 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 251 (Polychromatic418967fa.accept_11_2_4_9_1_484 90 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 251 (accept_3_2 88 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 251 (accept_3_2 85 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 251 (Polychromatic418967fa.accept_10_3_2_1_1_839 83 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 251 (accept_3_2 82 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 251
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 80 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 251 (accept_3_2 79 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 251 (accept_3_2 76 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 251 (accept_3_2 73 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 71 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 251 (accept_3_2 70 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 251
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 251 (accept_3_2 67 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 251 (accept_3_2 64 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 251 (accept_3_2 61 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 251 (accept_3_2 58 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 251
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 251 (accept_3_2 55 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 251 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 251 (accept_3_2 52 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 251 (accept_3_2 49 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 251 (accept_3_2 46 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 251 (accept_3_2 43 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 251 (accept_3_2 40 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 251 (accept_3_2 37 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 251 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 251 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 251 (accept_3_2 34 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 251 (accept_3_2 31 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 251 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 251 (accept_3_2 28 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 251
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 251 (accept_3_2 25 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 251 (accept_3_2 22 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 251
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 251 (accept_3_2 19 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 251 (Polychromatic418967fa.accept_13_5_1_4_1_3966 18 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 251 (Polychromatic418967fa.accept_16_1_12_11_1_2648 17 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 251 (accept_3_2 16 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 251 (accept_3_2 13 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 251 (Polychromatic418967fa.accept_17_11_7_13_1_11667 11 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 251 (accept_3_2 10 92 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 251
  (Polychromatic418967fa.accept_16_8_12_11_1_3697 8 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 251 (accept_3_2 7 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 92 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 251 (accept_3_2 4 92 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  92 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 251 (accept_3_2 1 92 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 251
  (allA_of_3_0 91 91 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 251 (allA_succ_of_accept 89 90 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 90 251 (accept_3_2 88 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  90 251 (Polychromatic418967fa.accept_20_7_10_11_1_9577 87 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 90 251 (Polychromatic418967fa.accept_13_8_12_4_1_4858 86 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 251 (accept_3_2 85 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 251 (Polychromatic418967fa.accept_11_7_2_9_1_480 84 90 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 90 251
  (Polychromatic418967fa.accept_13_5_12_4_1_449 83 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 90 251 (accept_3_2 82 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  90 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 90 251 (Polychromatic418967fa.accept_13_2_12_4_1_943 80 90 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 251 (accept_3_2 79 90 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 251 (Polychromatic418967fa.accept_17_10_5_13_1_12853 78 90 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 251 (accept_3_2 76 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  90 251 (Polychromatic418967fa.accept_14_5_6_13_1_3145 75 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 90 251 (Polychromatic418967fa.accept_20_14_10_11_1_2393 74 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 251 (accept_3_2 73 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 251 (Polychromatic418967fa.accept_13_7_12_4_1_450 72 90 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 251
  (Polychromatic418967fa.accept_27_17_9_8_1_9550 71 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 251 (accept_3_2 70 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  90 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 90 251 (Polychromatic418967fa.accept_13_3_12_4_1_110 68 90 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 251 (accept_3_2 67 90 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 251 (Polychromatic418967fa.accept_17_15_5_13_1_6626 66 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 90 251 (accept_3_2 64 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  90 251 (Polychromatic418967fa.accept_13_11_12_4_1_3945 63 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 90 251 (Polychromatic418967fa.accept_11_7_2_9_1_480 62 90 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 251 (accept_3_2 61 90 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 251 (Polychromatic418967fa.accept_13_8_12_4_1_4858 60 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 251
  (Polychromatic418967fa.accept_11_4_2_9_1_496 59 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 251 (accept_3_2 58 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  90 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 90 251 (Polychromatic418967fa.accept_19_18_14_4_1_8517 56 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 251 (accept_3_2 55 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 251 (Polychromatic418967fa.accept_13_2_12_4_1_943 54 90 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 251 (accept_3_2 52 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  90 251 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 90 251 (Polychromatic418967fa.accept_13_11_12_4_1_3945 50 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 251 (accept_3_2 49 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 251 (Polychromatic418967fa.accept_11_4_2_9_1_496 48 90 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 251
  (Polychromatic418967fa.accept_13_8_12_4_1_4858 47 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 251 (accept_3_2 46 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  90 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 90 251 (Polychromatic418967fa.accept_13_5_12_4_1_449 44 90 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 251 (accept_3_2 43 90 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 251 (Polychromatic418967fa.accept_13_3_12_4_1_110 42 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 251 (accept_3_2 40 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  90 251 (Polychromatic418967fa.accept_20_19_10_11_1_5107 39 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 90 251 (Polychromatic418967fa.accept_22_16_2_9_1_12064 38 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 251 (accept_3_2 37 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 251 (Polychromatic418967fa.accept_21_15_6_20_1_12272 36 90
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 251
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 35 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 90 251 (accept_3_2 34 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  90 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 90 251 (Polychromatic418967fa.accept_17_15_5_13_1_6626 32 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 251 (accept_3_2 31 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 251 (Polychromatic418967fa.accept_21_9_6_20_1_1903 30 90
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 251 (accept_3_2 28 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  90 251 (Polychromatic418967fa.accept_17_10_5_13_1_12853 27 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 90 251 (Polychromatic418967fa.accept_11_4_2_9_1_496 26 90 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 251 (accept_3_2 25 90 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 251 (Polychromatic418967fa.accept_13_11_12_4_1_3945 24 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 251
  (Polychromatic418967fa.accept_20_3_10_11_1_12493 23 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 90 251 (accept_3_2 22 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 90 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 251 (Polychromatic418967fa.accept_13_7_12_4_1_450 20 90 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 251 (accept_3_2 19 90 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 251 (Polychromatic418967fa.accept_11_7_2_9_1_480
  18 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 251 (accept_3_2 16 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 251 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 251 (Polychromatic418967fa.accept_20_14_10_11_1_2393 14 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 251 (accept_3_2 13 90 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 251 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 90
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 251
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 251 (accept_3_2 10 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 251 (Polychromatic418967fa.accept_13_8_12_4_1_4858 8 90 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 251 (accept_3_2 7 90 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 90 251 (Polychromatic418967fa.accept_24_6_18_11_1_6604 6 90 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 251 (accept_3_2 4 90 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 251 (Polychromatic418967fa.accept_13_3_12_4_1_110 3
  90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 251
  (Polychromatic418967fa.accept_13_2_12_4_1_943 2 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 251 (accept_3_2 1 90 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 251
  (allA_succ_of_accept 88 89 251 (accept_3_2 88 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 251 (Polychromatic418967fa.accept_11_10_1_9_1_2060 87 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 251 (accept_3_2 85 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 251 (Polychromatic418967fa.accept_13_6_11_4_1_938 84 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 251
  (Polychromatic418967fa.accept_19_7_13_4_1_1824 83 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 251 (accept_3_2 82 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 251 (Polychromatic418967fa.accept_13_2_11_4_1_445 80 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 251 (accept_3_2 79 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 251
  (Polychromatic418967fa.accept_13_12_11_4_1_3111 77 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 251 (accept_3_2 76 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 75 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 251 (accept_3_2 73 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 251 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 251 (accept_3_2 70 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 251 (Polychromatic418967fa.accept_16_5_9_11_1_3762 69 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 251 (Polychromatic418967fa.accept_10_8_9_1_1_189 68 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 251 (accept_3_2 67 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 251
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 251 (accept_3_2 64 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 251 (Polychromatic418967fa.accept_15_3_14_11_1_1579 63 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 251 (accept_3_2 61 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 251
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 59 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 251 (accept_3_2 58 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 251 (Polychromatic418967fa.accept_21_14_5_20_1_12299 56 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 251 (accept_3_2 55 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 251 (accept_3_2 52 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 251 (Polychromatic418967fa.accept_13_12_11_4_1_3111 51 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 251 (accept_3_2 49 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 251 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 251
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 47 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 251 (accept_3_2 46 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 251 (Polychromatic418967fa.accept_19_6_13_4_1_876 44 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 251 (accept_3_2 43 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 251
  (Polychromatic418967fa.accept_13_2_11_4_1_445 41 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 251 (accept_3_2 40 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 251 (accept_3_2 37 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 251
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 251 (accept_3_2 34 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 251 (Polychromatic418967fa.accept_13_7_11_4_1_2247 33 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 251 (accept_3_2 31 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 251 (accept_3_2 28 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 251 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 251 (accept_3_2 25 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 251 (Polychromatic418967fa.accept_22_2_1_9_1_10612 24 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 251
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 251 (accept_3_2 22 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 251 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 251 (Polychromatic418967fa.accept_13_7_11_4_1_2247 20 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 251 (accept_3_2 19 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 251
  (Polychromatic418967fa.accept_19_17_13_4_1_7081 17 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 251 (accept_3_2 16 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 251 (accept_3_2 13 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 251 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 251 (accept_3_2 10 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 251 (Polychromatic418967fa.accept_17_9_4_13_1_3057 9 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 251 (accept_3_2 7 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 251
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 251 (accept_3_2 4 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  251 (Polychromatic418967fa.accept_15_3_14_11_1_1579 3 89 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 251 (accept_3_2 1 89 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 251
  (allA_of_3_0 88 88 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 251 (allA_succ_of_accept 86 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 87 251 (accept_3_2 85 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  87 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 87 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 251 (accept_3_2 82 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 251 (accept_3_2 79 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 251 (Polychromatic418967fa.accept_11_1_10_9_1_871 78 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 251 (accept_3_2 76 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 251 (accept_3_2 73 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 251 (Polychromatic418967fa.accept_13_6_9_4_1_2288 71 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 251 (accept_3_2 70 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 251 (accept_3_2 67 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 251 (accept_3_2 64 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 251 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 251 (accept_3_2 61 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 251 (accept_3_2 58 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 251 (accept_3_2 55 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 251 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 251 (accept_3_2 52 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 251 (accept_3_2 49 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 251 (accept_3_2 46 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 251 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 251 (accept_3_2 43 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 251 (Polychromatic418967fa.accept_18_6_15_17_1_7363 42 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 251 (accept_3_2 40 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 251 (accept_3_2 37 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 251 (Polychromatic418967fa.accept_16_3_7_11_1_1723 35 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 251 (accept_3_2 34 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 87
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 251 (accept_3_2 31 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 251 (accept_3_2 28 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 251 (Polychromatic418967fa.accept_18_9_15_17_1_3497 27 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 251 (accept_3_2 25 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 251 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 251 (accept_3_2 22 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 251 (accept_3_2 19 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 251 (Polychromatic418967fa.accept_19_17_11_4_1_8452 17 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 251 (accept_3_2 16 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 251 (Polychromatic418967fa.accept_16_15_7_11_1_3760 15 87
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 251 (accept_3_2 13 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 251 (accept_3_2 10 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 251 (accept_3_2 7 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  251 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 87 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 251 (accept_3_2 4 87 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 251 (accept_3_2 1 87 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 251
  (allA_succ_of_accept 85 86 251 (accept_3_2 85 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 251 (accept_3_2 82 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 251
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 251 (accept_3_2 79 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 251 (accept_3_2 76 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 251 (accept_3_2 73 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 251 (accept_3_2 70 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 251 (accept_3_2 67 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 251 (accept_3_2 64 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 251
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 251 (accept_3_2 61 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 251 (accept_3_2 58 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 251 (accept_3_2 55 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 251 (Polychromatic418967fa.accept_19_16_10_4_1_9855 54 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 251 (accept_3_2 52 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 251 (accept_3_2 49 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 251 (accept_3_2 46 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 251 (accept_3_2 43 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 251 (accept_3_2 40 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 251
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 251 (accept_3_2 37 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 251 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 251 (accept_3_2 34 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 251 (accept_3_2 31 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 251 (accept_3_2 28 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 251
  (Polychromatic418967fa.accept_21_5_2_20_1_6081 26 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 251 (accept_3_2 25 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 251 (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 251 (accept_3_2 22 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 251 (accept_3_2 19 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 251 (accept_3_2 16 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 251
  (Polychromatic418967fa.accept_17_14_1_13_1_12898 14 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 86 251 (accept_3_2 13 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 86 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 86 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 86 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 86 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 251 (accept_3_2 10 86 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 251 (accept_3_2 7 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 86 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 251 (accept_3_2 4 86 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 86
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 251 (accept_3_2 1 86 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 251
  (allA_of_3_0 85 85 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 251 (allA_succ_of_accept 83 84 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 251 (accept_3_2 82 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 251 (Polychromatic418967fa.accept_15_6_9_11_1_858 81 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 251 (Polychromatic418967fa.accept_13_2_6_4_1_1593 80 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 251 (accept_3_2 79 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 251 (accept_3_2 76 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 251 (Polychromatic418967fa.accept_10_5_4_1_1_842 75 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 251 (accept_3_2 73 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 251 (Polychromatic418967fa.accept_13_7_6_4_1_933 72 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 251
  (Polychromatic418967fa.accept_8_7_4_3_1_156 71 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 251 (accept_3_2 70 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 251 (accept_3_2 67 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 251 (Polychromatic418967fa.accept_15_6_9_11_1_858 66 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 251 (accept_3_2 64 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 251 (Polychromatic418967fa.accept_13_10_6_4_1_1583 62 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 251 (accept_3_2 61 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 84 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 251 (accept_3_2 58 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 251 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 251 (accept_3_2 55 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 251 (Polychromatic418967fa.accept_13_2_6_4_1_1593 54 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 251
  (Polychromatic418967fa.accept_19_15_8_4_1_2962 53 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 251 (accept_3_2 52 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 251 (accept_3_2 49 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 251 (Polychromatic418967fa.accept_13_9_6_4_1_2243 48 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 251
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 251 (accept_3_2 46 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 251 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 251 (Polychromatic418967fa.accept_13_5_6_4_1_1582 44 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 251 (accept_3_2 43 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 251 (accept_3_2 40 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 251 (accept_3_2 37 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 251 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 251
  (Polychromatic418967fa.accept_10_5_4_1_1_842 35 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 251 (accept_3_2 34 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 251 (accept_3_2 31 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 251 (Polychromatic418967fa.accept_20_10_4_11_1_9652 30 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 251 (accept_3_2 28 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 251 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 251 (Polychromatic418967fa.accept_17_9_16_13_1_6636 26 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 251 (accept_3_2 25 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 84 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 251
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 251 (accept_3_2 22 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 251 (Polychromatic418967fa.accept_15_6_9_11_1_858 21 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 251 (accept_3_2 19 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 251 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 251
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 251 (accept_3_2 16 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 251 (accept_3_2 13 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 251 (Polychromatic418967fa.accept_16_12_4_11_1_3710 12 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 251 (accept_3_2 10 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 251 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 251 (Polychromatic418967fa.accept_16_8_4_11_1_2687 8 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 251 (accept_3_2 7 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 84 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 251 (accept_3_2 4 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  251 (Polychromatic418967fa.accept_17_3_16_13_1_6635 3 84 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 84 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 251 (accept_3_2 1 84 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 251
  (allA_succ_of_accept 82 83 251 (accept_3_2 82 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 251 (Polychromatic418967fa.accept_23_12_14_21_1_15132 81 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 251 (Polychromatic418967fa.accept_11_3_6_9_1_1378 80 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 251 (accept_3_2 79 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 251 (accept_3_2 76 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 251 (Polychromatic418967fa.accept_13_9_5_4_1_1591 74 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 251 (accept_3_2 73 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 251 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 251
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 71 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 251 (accept_3_2 70 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 251 (accept_3_2 67 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 251
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 251 (accept_3_2 64 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 251 (Polychromatic418967fa.accept_15_3_8_11_1_4386 63 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 251 (Polychromatic418967fa.accept_10_2_3_1_1_481 62 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 251 (accept_3_2 61 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 251 (accept_3_2 58 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 251 (Polychromatic418967fa.accept_16_8_3_11_1_4763 56 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 251 (accept_3_2 55 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 251 (Polychromatic418967fa.accept_13_2_5_4_1_3926 54 83 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 251
  (Polychromatic418967fa.accept_13_1_5_4_1_463 53 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 251 (accept_3_2 52 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 251 (accept_3_2 49 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 251
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 251 (accept_3_2 46 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 251 (Polychromatic418967fa.accept_13_6_5_4_1_3924 45 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 251 (Polychromatic418967fa.accept_29_15_25_19_1_15131 44 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 251 (accept_3_2 43 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 83 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 251 (accept_3_2 40 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 251 (Polychromatic418967fa.accept_10_8_3_1_1_1316 38 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 251 (accept_3_2 37 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 251 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 251
  (Polychromatic418967fa.accept_13_9_5_4_1_1591 35 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 251 (accept_3_2 34 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 251 (accept_3_2 31 83 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 251
  (Polychromatic418967fa.accept_23_6_14_21_1_13614 29 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 83 251 (accept_3_2 28 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 83 251 (Polychromatic418967fa.accept_13_1_5_4_1_463 27 83 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 251 (Polychromatic418967fa.accept_22_4_17_9_1_15130 26 83
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 251 (accept_3_2 25 83 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 24
  83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 251 (accept_3_2 22 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 251 (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 251 (accept_3_2 19 83 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 251 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 83 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 251
  (Polychromatic418967fa.accept_31_17_21_3_1_15129 17 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 83 251 (accept_3_2 16 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 83 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 83 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 251 (accept_3_2 13 83 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 12
  83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 251
  (Polychromatic418967fa.accept_17_11_15_13_1_11717 11 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 83 251 (accept_3_2 10 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 83 251 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 83 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 251 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 83 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 251 (accept_3_2 7 83 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 251 (accept_3_2 4 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  251 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 83 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 251 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 83 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 251 (accept_3_2 1 83 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 251 (allA_of_3_0 82 82 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 251
  (allA_succ_of_accept 80 81 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 251 (accept_3_2 79 81 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 251 (Polychromatic418967fa.accept_13_12_3_4_1_928
  77 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 251 (accept_3_2 76
  81 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 81 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 251 (accept_3_2 73 81 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 251
  (Polychromatic418967fa.accept_22_5_15_9_1_10649 71 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 81 251 (accept_3_2 70 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  81 251 (Polychromatic418967fa.accept_15_9_6_11_1_1586 69 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 81 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 251 (accept_3_2 67 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 251 (accept_3_2 64 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  81 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 251 (accept_3_2 61 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 251 (Polychromatic418967fa.accept_16_12_1_11_1_5958 60 81 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 251 (accept_3_2 58 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 251 (Polychromatic418967fa.accept_11_2_4_9_1_484 57 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 251 (accept_3_2 55 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 251
  (Polychromatic418967fa.accept_13_1_3_4_1_925 53 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 251 (accept_3_2 52 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 251 (accept_3_2 49 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 251 (Polychromatic418967fa.accept_15_3_6_11_1_855 48 81 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 251 (accept_3_2 46 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 251 (accept_3_2 43 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 251
  (Polychromatic418967fa.accept_24_17_9_11_1_13548 41 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 81 251 (accept_3_2 40 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 81 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 81 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 251 (accept_3_2 37 81 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 251
  (Polychromatic418967fa.accept_20_16_1_11_1_9647 36 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 81 251 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 81 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 251 (accept_3_2 34 81 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 81 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 32
  81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 251 (accept_3_2 31 81
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27
  30 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 251
  (Polychromatic418967fa.accept_22_7_15_9_1_5710 29 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 251 (accept_3_2 28 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 251 (accept_3_2 25 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 251 (accept_3_2 22 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 251 (Polychromatic418967fa.accept_19_2_5_4_1_15128 21 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 251 (accept_3_2 19 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 251 (accept_3_2 16 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 251 (accept_3_2 13 81 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 251
  (Polychromatic418967fa.accept_21_11_18_20_1_1877 11 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 81 251 (accept_3_2 10 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 81 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 251 (accept_3_2 7 81 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 251 (accept_3_2 4 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  251 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 81 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 251 (accept_3_2 1 81 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 251 (allA_succ_of_accept 79 80 251 (accept_3_2 79 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 80 251 (Polychromatic418967fa.accept_23_9_11_21_1_5259 78 80 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 80 251 (Polychromatic418967fa.accept_13_12_2_4_1_3131 77 80
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 251 (accept_3_2 76 80 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 75
  80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 251 (accept_3_2 73 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 251 (Polychromatic418967fa.accept_13_6_2_4_1_923 71 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 251 (accept_3_2 70 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 251
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 68 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 251 (accept_3_2 67 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 251 (Polychromatic418967fa.accept_15_6_5_11_1_2378 66 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 251 (accept_3_2 64 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 251 (accept_3_2 61 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 251 (Polychromatic418967fa.accept_14_3_10_13_1_339 59 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 251 (accept_3_2 58 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 251
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 56 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 251 (accept_3_2 55 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 251 (Polychromatic418967fa.accept_15_9_5_11_1_5416 54 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 251 (accept_3_2 52 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 251
  (Polychromatic418967fa.accept_11_6_3_9_1_906 50 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 251 (accept_3_2 49 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 251 (Polychromatic418967fa.accept_23_2_11_21_1_11953 48 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 251 (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 251 (accept_3_2 46 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 251 (accept_3_2 43 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 251 (Polychromatic418967fa.accept_22_20_14_9_1_12125 42 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 251 (Polychromatic418967fa.accept_18_5_8_17_1_3478 41 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 251 (accept_3_2 40 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 251 (accept_3_2 37 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 251 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 251 (Polychromatic418967fa.accept_17_1_12_13_1_448 35 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 251 (accept_3_2 34 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 251 (accept_3_2 31 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 251 (Polychromatic418967fa.accept_21_8_17_20_1_3142 29 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 251 (accept_3_2 28 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 251 (accept_3_2 25 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 251 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 251 (accept_3_2 22 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 251
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 20 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 251 (accept_3_2 19 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 251 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 251 (accept_3_2 16 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 251 (accept_3_2 13 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 251 (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 251 (accept_3_2 10 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 251
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 251 (accept_3_2 7 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  251 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 80 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 251 (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 80 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 251 (accept_3_2 4 80 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 80
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 251 (accept_3_2 1 80 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 251 (allA_of_3_0 79
  79 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 251 (allA_succ_of_accept 77 78 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 251 (accept_3_2 76 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 251 (accept_3_2 73 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 78 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 251
  (Polychromatic418967fa.accept_17_3_10_13_1_2021 71 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 251 (accept_3_2 70 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 251 (accept_3_2 67 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 78 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 251 (accept_3_2 64 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 251 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 251 (Polychromatic418967fa.accept_19_5_2_4_1_9840 62 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 251 (accept_3_2 61 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 251 (Polychromatic418967fa.accept_17_9_10_13_1_6698 60 78 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 251 (accept_3_2 58 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 251 (accept_3_2 55 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 78 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 251 (accept_3_2 52 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 251 (accept_3_2 49 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 78 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 251
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 251 (accept_3_2 46 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 251 (accept_3_2 43 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 251 (Polychromatic418967fa.accept_22_20_12_9_1_15127 42 78 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 251 (accept_3_2 40 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 251 (accept_3_2 37 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 251 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 78 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 251
  (Polychromatic418967fa.accept_14_7_8_13_1_3161 35 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 251 (accept_3_2 34 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 251 (accept_3_2 31 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 78 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 251 (accept_3_2 28 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 251 (Polychromatic418967fa.accept_20_7_18_11_1_5080 27 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 251 (accept_3_2 25 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 251 (Polychromatic418967fa.accept_19_5_2_4_1_9840 24 78 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 251 (accept_3_2 22 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 251 (accept_3_2 19 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 251 (Polychromatic418967fa.accept_19_18_2_4_1_7039 18 78 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 251 (accept_3_2 16 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 251 (Polychromatic418967fa.accept_18_15_6_17_1_2386 15 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 251 (accept_3_2 13 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 78 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 251 (accept_3_2 10 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 251 (Polychromatic418967fa.accept_15_8_3_11_1_849 8 78 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 251 (accept_3_2 7 78 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 251 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 78 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 251 (accept_3_2 4 78 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 251 (accept_3_2 1 78 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 251
  (allA_succ_of_accept 76 77 251 (accept_3_2 76 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 251 (accept_3_2 73 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 251 (Polychromatic418967fa.accept_13_7_12_4_1_450 72 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 251
  (Polychromatic418967fa.accept_14_1_7_13_1_333 71 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 251 (accept_3_2 70 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 251 (Polychromatic418967fa.accept_13_3_12_4_1_110 68 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 251 (accept_3_2 67 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 251 (accept_3_2 64 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 251 (Polychromatic418967fa.accept_13_11_12_4_1_3945 63 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 251 (accept_3_2 61 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 251
  (Polychromatic418967fa.accept_13_7_12_4_1_450 59 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 251 (accept_3_2 58 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 251 (accept_3_2 55 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 251
  (Polychromatic418967fa.accept_19_15_1_4_1_4238 53 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 251 (accept_3_2 52 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 251 (accept_3_2 49 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 251 (accept_3_2 46 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 251 (Polychromatic418967fa.accept_19_7_1_4_1_12606 45 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 251 (Polychromatic418967fa.accept_10_4_7_1_1_471 44 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 251 (accept_3_2 43 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 251
  (Polychromatic418967fa.accept_13_2_12_4_1_943 41 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 251 (accept_3_2 40 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 251 (accept_3_2 37 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 251 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 251
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 251 (accept_3_2 34 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 251 (Polychromatic418967fa.accept_21_11_14_20_1_12235 32 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 251 (accept_3_2 31 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 251 (accept_3_2 28 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 251 (Polychromatic418967fa.accept_17_10_9_13_1_6644 27 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 251 (accept_3_2 25 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 251
  (Polychromatic418967fa.accept_21_2_14_20_1_841 23 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 251 (accept_3_2 22 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 251 (accept_3_2 19 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 251
  (Polychromatic418967fa.accept_19_17_1_4_1_7022 17 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 251 (accept_3_2 16 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 251 (accept_3_2 13 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 251 (accept_3_2 10 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 251 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 251 (Polychromatic418967fa.accept_13_8_12_4_1_4858 8 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 251 (accept_3_2 7 77 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 251
  (Polychromatic418967fa.accept_13_5_12_4_1_449 5 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 251 (accept_3_2 4 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  251 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 77 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 251 (accept_3_2 1 77 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 251 (allA_of_3_0 76 76 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 251 (allA_succ_of_accept 74 75
  251 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 251 (accept_3_2 73 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 251 (Polychromatic418967fa.accept_13_7_10_4_1_919 72 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 251 (accept_3_2 70 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 251 (accept_3_2 67 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 251 (Polychromatic418967fa.accept_10_6_5_1_1_482 66 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 251 (accept_3_2 64 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 251 (Polychromatic418967fa.accept_13_11_10_4_1_1565 63 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 251 (accept_3_2 61 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 251 (accept_3_2 58 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 251 (accept_3_2 55 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 251 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 251 (accept_3_2 52 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 251 (accept_3_2 49 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 251 (Polychromatic418967fa.accept_14_6_5_13_1_367 48 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 251 (accept_3_2 46 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 251 (accept_3_2 43 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 251 (accept_3_2 40 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 251 (accept_3_2 37 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 251 (Polychromatic418967fa.accept_26_9_23_17_1_15126 35 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 251 (accept_3_2 34 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 251 (accept_3_2 31 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 251 (Polychromatic418967fa.accept_19_11_18_4_1_2957 30 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 251 (accept_3_2 28 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 251 (Polychromatic418967fa.accept_13_1_10_4_1_954 27 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 251 (accept_3_2 25 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 251 (accept_3_2 22 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 251 (accept_3_2 19 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 251 (Polychromatic418967fa.accept_19_17_18_4_1_12571 17 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 251 (accept_3_2 16 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 75 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 251 (accept_3_2 13 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 251 (Polychromatic418967fa.accept_27_12_21_8_1_15125 12 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 251 (accept_3_2 10 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 251 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 75 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 251 (accept_3_2 7 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 75 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 75 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 251 (accept_3_2 4 75 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 251 (Polychromatic418967fa.accept_19_3_18_4_1_8492 3 75 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 251 (accept_3_2 1 75 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 251 (allA_succ_of_accept
  73 74 251 (accept_3_2 73 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 251 (Polychromatic418967fa.accept_13_6_9_4_1_2288 71 74 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 251 (accept_3_2 70 74 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 68
  74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 251 (accept_3_2 67 74
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 251 (accept_3_2 64 74 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 251
  (Polychromatic418967fa.accept_17_11_6_13_1_10553 62 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 74 251 (accept_3_2 61 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 74 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 74 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 74 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 74 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 251 (accept_3_2 58 74 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 251 (accept_3_2 55 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 251 (accept_3_2 52 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 74 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 251 (accept_3_2 49 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 251 (accept_3_2 46 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 251 (accept_3_2 43 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 251 (accept_3_2 40 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 74 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 251 (accept_3_2 37 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 251 (Polychromatic418967fa.accept_17_2_6_13_1_2056 36 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 251 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 251 (accept_3_2 34 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 251 (accept_3_2 31 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 251 (accept_3_2 28 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 251 (accept_3_2 25 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 251 (accept_3_2 22 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 251 (accept_3_2 19 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 251 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 251 (accept_3_2 16 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 251 (accept_3_2 13 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 251 (Polychromatic418967fa.accept_17_11_6_13_1_10553 11 74 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 251 (accept_3_2 10 74 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 251 (accept_3_2 7 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 251 (accept_3_2 4 74 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  74 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 251 (accept_3_2 1 74 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 251 (allA_of_3_0 73 73 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 251 (allA_succ_of_accept 71 72 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 251 (accept_3_2 70 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 251 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 251 (Polychromatic418967fa.accept_13_3_7_4_1_435 68 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 251 (accept_3_2 67 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 251
  (Polychromatic418967fa.accept_17_14_4_13_1_3018 65 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 251 (accept_3_2 64 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 251 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 251 (Polychromatic418967fa.accept_13_10_7_4_1_2262 62 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 251 (accept_3_2 61 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 72 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 251
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 251 (accept_3_2 58 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 251 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 251 (accept_3_2 55 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 251 (Polychromatic418967fa.accept_17_3_4_13_1_2030 54 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 251 (accept_3_2 52 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 251 (Polychromatic418967fa.accept_13_12_7_4_1_3124 51 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 251 (accept_3_2 49 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 251 (Polychromatic418967fa.accept_13_9_7_4_1_953 48 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 251
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 251 (accept_3_2 46 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 251 (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 251 (accept_3_2 43 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 251 (Polychromatic418967fa.accept_13_3_7_4_1_435 42 72 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 251
  (Polychromatic418967fa.accept_20_1_12_11_1_3778 41 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 251 (accept_3_2 40 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 251 (accept_3_2 37 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 251
  (Polychromatic418967fa.accept_13_9_7_4_1_953 35 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 251 (accept_3_2 34 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 251 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 251 (accept_3_2 31 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 251 (Polychromatic418967fa.accept_19_11_15_4_1_7010 30 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 251 (accept_3_2 28 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 251 (Polychromatic418967fa.accept_19_8_15_4_1_2953 27 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 251 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 251 (accept_3_2 25 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 251
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 251 (accept_3_2 22 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 251 (Polychromatic418967fa.accept_16_5_8_11_1_9582 21 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 251 (Polychromatic418967fa.accept_16_4_8_11_1_5961 20 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 251 (accept_3_2 19 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 72 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 251
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 251 (accept_3_2 16 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 251 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 251 (accept_3_2 13 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 251 (Polychromatic418967fa.accept_13_12_7_4_1_3124 12 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 251 (accept_3_2 10 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 251 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 251 (accept_3_2 7 72 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 251 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 72 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 251
  (Polychromatic418967fa.accept_16_5_8_11_1_9582 5 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 251 (accept_3_2 4 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 251 (Polychromatic418967fa.accept_21_2_9_20_1_9260 2 72 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 251 (accept_3_2 1 72 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 251
  (allA_succ_of_accept 70 71 251 (accept_3_2 70 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 251 (Polychromatic418967fa.accept_16_5_7_11_1_2664 69 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 251 (accept_3_2 67 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 251 (Polychromatic418967fa.accept_16_2_7_11_1_1698 66 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 251 (accept_3_2 64 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 251 (Polychromatic418967fa.accept_13_11_6_4_1_3121 63 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 251 (Polychromatic418967fa.accept_11_7_5_9_1_884 62 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 251 (accept_3_2 61 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 251
  (Polychromatic418967fa.accept_13_7_6_4_1_933 59 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 251 (accept_3_2 58 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 251 (Polychromatic418967fa.accept_13_5_6_4_1_1582 57 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 251 (Polychromatic418967fa.accept_19_18_14_4_1_8517 56 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 251 (accept_3_2 55 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 71 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 251
  (Polychromatic418967fa.accept_16_5_7_11_1_2664 53 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 251 (accept_3_2 52 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 251 (Polychromatic418967fa.accept_13_11_6_4_1_3121 50 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 251 (accept_3_2 49 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 251 (Polychromatic418967fa.accept_13_9_6_4_1_2243 48 71 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 251
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 251 (accept_3_2 46 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 251 (Polychromatic418967fa.accept_19_7_14_4_1_4268 45 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 251 (accept_3_2 43 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 251 (Polychromatic418967fa.accept_17_8_3_13_1_5372 42 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 251
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 41 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 251 (accept_3_2 40 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 251 (Polychromatic418967fa.accept_23_16_2_21_1_11948 39 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 251 (Polychromatic418967fa.accept_17_4_3_13_1_6692 38 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 251 (accept_3_2 37 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 71 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 251
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 35 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 251 (accept_3_2 34 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 251 (Polychromatic418967fa.accept_19_13_14_4_1_5621 32 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 251 (accept_3_2 31 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 71 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 251
  (Polychromatic418967fa.accept_11_7_5_9_1_884 29 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 251 (accept_3_2 28 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 251 (Polychromatic418967fa.accept_17_10_3_13_1_6639 27 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 251 (accept_3_2 25 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 251 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 251 (accept_3_2 22 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 251 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 251 (accept_3_2 19 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 251 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 251
  (Polychromatic418967fa.accept_21_17_8_20_1_7805 17 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 251 (accept_3_2 16 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 251 (Polychromatic418967fa.accept_13_2_6_4_1_1593 15 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 251 (Polychromatic418967fa.accept_22_14_5_9_1_15124 14 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 251 (accept_3_2 13 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 251
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 251 (accept_3_2 10 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 251 (Polychromatic418967fa.accept_17_8_3_13_1_5372 8 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 251 (accept_3_2 7 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 251 (Polychromatic418967fa.accept_26_6_19_17_1_15123 6 71 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 251
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 251 (accept_3_2 4 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  251 (Polychromatic418967fa.accept_16_3_7_11_1_1723 3 71 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 251 (accept_3_2 1 71 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 70 251 (allA_of_3_0 70 70 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 251
  (allA_succ_of_accept 68 69 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 251 (accept_3_2 67 69 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 65
  69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 251 (accept_3_2 64 69
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 251
  (Polychromatic418967fa.accept_12_3_9_11_1_231 63 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 251 (accept_3_2 61 69 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 251 (Polychromatic418967fa.accept_18_6_15_17_1_7363 60 69 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 251 (accept_3_2 58 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  69 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 69 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 251 (accept_3_2 55 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 251
  (Polychromatic418967fa.accept_17_2_1_13_1_6670 53 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 251 (accept_3_2 52 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  69 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 251 (accept_3_2 49 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 251 (accept_3_2 46 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  69 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 69 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 251 (accept_3_2 43 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 251 (accept_3_2 40 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  69 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 251 (accept_3_2 37 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 251 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 69 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 251
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 251 (accept_3_2 34 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  69 251 (Polychromatic418967fa.accept_22_11_3_9_1_15122 33 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 69 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 251 (accept_3_2 31 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 251 (accept_3_2 28 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 251 (accept_3_2 25 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 251 (Polychromatic418967fa.accept_16_8_5_11_1_4776 24 69 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 251 (accept_3_2 22 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 251 (accept_3_2 19 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 251
  (Polychromatic418967fa.accept_11_6_3_9_1_906 17 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 251 (accept_3_2 16 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 251 (accept_3_2 13 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 251 (accept_3_2 10 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 251 (Polychromatic418967fa.accept_16_9_5_11_1_3776 9 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 251 (accept_3_2 7 69 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 251 (accept_3_2 4 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 69 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 251 (accept_3_2 1 69 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 251
  (allA_succ_of_accept 67 68 251 (accept_3_2 67 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  68 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 68 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 251 (accept_3_2 64 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 251
  (Polychromatic418967fa.accept_11_7_2_9_1_480 62 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 251 (accept_3_2 61 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 251 (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 251 (accept_3_2 58 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 251 (accept_3_2 55 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 251 (Polychromatic418967fa.accept_16_6_4_11_1_1719 54 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 251 (accept_3_2 52 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 251 (accept_3_2 49 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 251 (accept_3_2 46 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 251
  (Polychromatic418967fa.accept_16_12_4_11_1_3710 44 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 251 (accept_3_2 43 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 251 (Polychromatic418967fa.accept_16_9_4_11_1_2661 41 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 251 (accept_3_2 40 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 251 (accept_3_2 37 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 251 (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 251 (accept_3_2 34 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 251 (accept_3_2 31 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 251 (accept_3_2 28 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 251
  (Polychromatic418967fa.accept_11_4_2_9_1_496 26 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 251 (accept_3_2 25 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 251 (accept_3_2 22 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 251 (accept_3_2 19 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 251 (Polychromatic418967fa.accept_19_17_11_4_1_8452 17 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 251 (accept_3_2 16 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 251 (accept_3_2 13 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 251 (accept_3_2 10 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 251 (accept_3_2 7 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 68 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 251 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 68 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 251 (accept_3_2 4 68 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 68
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 251 (accept_3_2 1 68 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 251 (allA_of_3_0 67 67 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 251 (allA_succ_of_accept 65 66 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 251 (accept_3_2 64 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 251 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 251 (accept_3_2 61 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 66 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 251 (accept_3_2 58 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 251 (accept_3_2 55 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 251 (Polychromatic418967fa.accept_15_9_6_11_1_1586 54 66 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 251 (accept_3_2 52 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 251 (accept_3_2 49 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 251 (Polychromatic418967fa.accept_15_3_6_11_1_855 48 66 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 251 (accept_3_2 46 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 251 (accept_3_2 43 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 66 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 251 (accept_3_2 40 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 251 (accept_3_2 37 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 251 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 66 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 251
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 251 (accept_3_2 34 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 251 (accept_3_2 31 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 66 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 251 (accept_3_2 28 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 251 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 251 (Polychromatic418967fa.accept_23_3_20_21_1_15121 26 66 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 251 (accept_3_2 25 66 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 66 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 251 (accept_3_2 22 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 251 (accept_3_2 19 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 66 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 251 (accept_3_2 16 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 251 (accept_3_2 13 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 66 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 251 (accept_3_2 10 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 251 (Polychromatic418967fa.accept_17_8_15_13_1_7942 8 66 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 251 (accept_3_2 7 66 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 66 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 66 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 251 (accept_3_2 4 66 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 251 (Polychromatic418967fa.accept_13_3_1_4_1_945 3
  66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 251 (accept_3_2 1 66 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 251 (allA_succ_of_accept 64 65 251
  (accept_3_2 64 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 251
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 251 (accept_3_2 61 65 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 59
  65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 251 (accept_3_2 58 65
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 251 (Polychromatic418967fa.accept_7_1_2_6_1_55
  57 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 251
  (Polychromatic418967fa.accept_10_6_5_1_1_482 56 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 65 251 (accept_3_2 55 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  65 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 65 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 251 (accept_3_2 52 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 65 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 251 (accept_3_2 49 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 251 (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 65 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 251 (accept_3_2 46 65 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 65 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 251
  (Polychromatic418967fa.accept_10_4_5_1_1_497 44 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 251 (accept_3_2 43 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 251 (accept_3_2 40 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 65 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 251 (accept_3_2 37 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 251 (Polychromatic418967fa.accept_17_1_14_13_1_7966 35 65 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 251 (accept_3_2 34 65 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 65 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 251 (accept_3_2 31 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 251 (accept_3_2 28 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 251 (Polychromatic418967fa.accept_17_10_14_13_1_12880 27 65 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 251 (accept_3_2 25 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 251 (accept_3_2 22 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 65 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 251
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 20 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 251 (accept_3_2 19 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 251 (accept_3_2 16 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 65 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 251 (accept_3_2 13 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 251 (accept_3_2 10 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 251 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 251 (accept_3_2 7 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 65 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 251 (accept_3_2 4 65 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 65 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 251 (accept_3_2 1 65 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 251 (allA_of_3_0 64 64 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 251 (allA_succ_of_accept 62 63 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 251 (accept_3_2 61 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 251 (Polychromatic418967fa.accept_13_7_11_4_1_2247 59 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 251 (accept_3_2 58 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 63
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 251 (accept_3_2 55 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 251 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 251 (Polychromatic418967fa.accept_15_8_3_11_1_849 53 63 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 251 (accept_3_2 52 63 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 251 (Polychromatic418967fa.accept_13_12_11_4_1_3111 51 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 251 (accept_3_2 49 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 251 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 251 (Polychromatic418967fa.accept_13_8_11_4_1_1553 47 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 251 (accept_3_2 46 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 63
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 251 (accept_3_2 43 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 251 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 251 (Polychromatic418967fa.accept_13_2_11_4_1_445 41 63 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 251 (accept_3_2 40 63 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 251 (Polychromatic418967fa.accept_16_7_15_11_1_951 39 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 251 (accept_3_2 37 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 251 (Polychromatic418967fa.accept_16_3_15_11_1_2676 35 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 251 (accept_3_2 34 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 251 (accept_3_2 31 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 251 (Polychromatic418967fa.accept_18_12_9_17_1_7428 30 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 251 (Polychromatic418967fa.accept_14_1_7_13_1_333 29 63 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 251 (accept_3_2 28 63 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 251 (Polychromatic418967fa.accept_23_4_17_21_1_15120 27 63 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 251 (accept_3_2 25 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 251 (Polychromatic418967fa.accept_19_5_6_4_1_8480 24 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 251 (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 251 (accept_3_2 22 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 251 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 63 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 251 (accept_3_2 19 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 251 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 251 (Polychromatic418967fa.accept_16_1_15_11_1_356 17 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 251 (accept_3_2 16 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 251 (Polychromatic418967fa.accept_13_2_11_4_1_445 15 63 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 251 (accept_3_2 13 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 251 (Polychromatic418967fa.accept_17_11_12_13_1_3030 11 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 251 (accept_3_2 10 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 63 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 251 (accept_3_2 7 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  251 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 251 (Polychromatic418967fa.accept_19_5_6_4_1_8480 5 63 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 251 (accept_3_2 4 63 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 251 (Polychromatic418967fa.accept_16_3_15_11_1_2676 3 63 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 251 (accept_3_2 1 63 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 251 (allA_succ_of_accept 61 62 251
  (accept_3_2 61 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 251
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 251 (Polychromatic418967fa.accept_10_9_2_1_1_840 59 62 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 251 (accept_3_2 58 62 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 251 (Polychromatic418967fa.accept_10_6_2_1_1_494
  56 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 251 (accept_3_2 55
  62 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 251
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 54 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 251 (accept_3_2 52 62 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 251
  (Polychromatic418967fa.accept_13_11_10_4_1_1565 50 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 251 (accept_3_2 49 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 251 (Polychromatic418967fa.accept_23_2_16_21_1_13618 48 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 251 (Polychromatic418967fa.accept_13_8_10_4_1_2270 47 62 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 251 (accept_3_2 46 62 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 251 (accept_3_2 43 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 251 (Polychromatic418967fa.accept_22_20_18_9_1_15119 42 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 251 (accept_3_2 40 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 251
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 38 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 251 (accept_3_2 37 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 251 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 251 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 251 (accept_3_2 34 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 251 (accept_3_2 31 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 251 (Polychromatic418967fa.accept_22_8_18_9_1_5631 30 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 251 (accept_3_2 28 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 251
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 251 (accept_3_2 25 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 251 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 251 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 251 (accept_3_2 22 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 251 (accept_3_2 19 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 251 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 251 (accept_3_2 16 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 251
  (Polychromatic418967fa.accept_13_1_10_4_1_954 14 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 251 (accept_3_2 13 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 251 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 251 (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 62 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 251 (accept_3_2 10 62 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 251 (accept_3_2 7 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  251 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 251 (accept_3_2 4 62 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 251 (Polychromatic418967fa.accept_11_2_7_9_1_890 2
  62 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 251 (accept_3_2 1 62 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 251 (allA_of_3_0 61 61 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 251 (allA_succ_of_accept 59 60 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 251 (accept_3_2 58 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 251 (accept_3_2 55 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 60 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 251
  (Polychromatic418967fa.accept_21_11_18_20_1_1877 53 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 60 251 (accept_3_2 52 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 60 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 60 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 251 (accept_3_2 49 60 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 48
  60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 251 (accept_3_2 46 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 251 (accept_3_2 43 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 251 (Polychromatic418967fa.accept_16_10_12_11_1_346 42 60 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 251 (accept_3_2 40 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 251 (accept_3_2 37 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 251 (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 60 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 251
  (Polychromatic418967fa.accept_13_9_8_4_1_937 35 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 251 (accept_3_2 34 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 251 (accept_3_2 31 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 60 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 251 (accept_3_2 28 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 251 (Polychromatic418967fa.accept_17_10_9_13_1_6644 27 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 251 (accept_3_2 25 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 60 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 251 (accept_3_2 22 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 251 (accept_3_2 19 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 251 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 60 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 251 (accept_3_2 16 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 251 (accept_3_2 13 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 60 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 251 (accept_3_2 10 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 251 (Polychromatic418967fa.accept_16_8_12_11_1_3697 8 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 251 (accept_3_2 7 60 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 251 (Polychromatic418967fa.accept_19_6_3_4_1_7040 6 60 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 251 (accept_3_2 4 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  251 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 60 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 251 (accept_3_2 1 60 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 251
  (allA_succ_of_accept 58 59 251 (accept_3_2 58 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 251 (accept_3_2 55 59 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 251 (Polychromatic418967fa.accept_17_3_8_13_1_5361 54 59 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 251 (accept_3_2 52 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 251 (Polychromatic418967fa.accept_13_11_7_4_1_1561 50 59 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 251 (accept_3_2 49 59 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 59 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 251 (accept_3_2 46 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 59 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 251 (accept_3_2 43 59 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 251
  (Polychromatic418967fa.accept_25_16_9_1_1_15118 41 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 251 (accept_3_2 40 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 251 (accept_3_2 37 59 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 251 (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 59 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 251
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 251 (accept_3_2 34 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 59 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 251 (accept_3_2 31 59 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 251 (accept_3_2 28 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 251 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 251 (Polychromatic418967fa.accept_18_8_5_17_1_1388 26 59 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 251 (accept_3_2 25 59 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 251 (accept_3_2 22 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 59 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 251 (accept_3_2 19 59 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 59 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 251
  (Polychromatic418967fa.accept_19_17_2_4_1_4278 17 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 251 (accept_3_2 16 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 251 (Polychromatic418967fa.accept_19_14_2_4_1_8473 14 59 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 251 (accept_3_2 13 59 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 251 (accept_3_2 10 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 251 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 59 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 251 (accept_3_2 7 59 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 59 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 5
  59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 251 (accept_3_2 4 59 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 59
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 251 (accept_3_2 1 59 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  251))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 251 (allA_of_3_0 58 58 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 57 251 (allA_succ_of_accept 56 57 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 251 (accept_3_2 55 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 251 (Polychromatic418967fa.accept_13_1_5_4_1_463 53 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 251 (accept_3_2 52 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 57 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 251 (accept_3_2 49 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 251 (Polychromatic418967fa.accept_11_4_2_9_1_496 48 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 251 (accept_3_2 46 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 251 (Polychromatic418967fa.accept_13_6_5_4_1_3924 45 57 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 251 (accept_3_2 43 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 251 (accept_3_2 40 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 57 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 251 (accept_3_2 37 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 251 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 251 (Polychromatic418967fa.accept_13_9_5_4_1_1591 35 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 251 (accept_3_2 34 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 251 (accept_3_2 31 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 251 (accept_3_2 28 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 57 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 251 (accept_3_2 25 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 251 (accept_3_2 22 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 251 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 57 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 251 (accept_3_2 19 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 251 (Polychromatic418967fa.accept_23_17_11_21_1_10511 17 57 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 251 (accept_3_2 16 57 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 251 (accept_3_2 13 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 251 (accept_3_2 10 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 251 (accept_3_2 7 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 57 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 251 (accept_3_2 4 57 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 57 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 251 (accept_3_2 1 57 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 251 (allA_succ_of_accept 55 56 251 (accept_3_2 55 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 251 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 56 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 251 (Polychromatic418967fa.accept_16_5_8_11_1_9582 53 56
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 251 (accept_3_2 52 56 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 251 (accept_3_2 49 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 251 (Polychromatic418967fa.accept_10_7_6_1_1_486 47 56 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 251 (accept_3_2 46 56 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 251
  (Polychromatic418967fa.accept_16_12_8_11_1_2695 44 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 251 (accept_3_2 43 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 251 (accept_3_2 40 56 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 251 (accept_3_2 37 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 251 (Polychromatic418967fa.accept_16_4_8_11_1_5961 36 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 251 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 56 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 251 (accept_3_2 34 56 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 251 (accept_3_2 31 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 251 (Polychromatic418967fa.accept_16_13_8_11_1_4785 29 56 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 251 (accept_3_2 28 56 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 251 (accept_3_2 25 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 251 (accept_3_2 22 56 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 251
  (Polychromatic418967fa.accept_16_4_8_11_1_5961 20 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 251 (accept_3_2 19 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 251 (Polychromatic418967fa.accept_20_18_16_11_1_13777 18 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 251 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 56 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 251 (accept_3_2 16 56 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 251 (accept_3_2 13 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 251 (Polychromatic418967fa.accept_18_11_2_17_1_3490 11 56 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 251 (accept_3_2 10 56 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 251
  (Polychromatic418967fa.accept_17_8_5_13_1_4158 8 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 251 (accept_3_2 7 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 251 (accept_3_2 4 56 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  56 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 251 (accept_3_2 1 56 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 251))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 251 (allA_of_3_0 55 55 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 251
  (allA_succ_of_accept 53 54 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 251 (accept_3_2 52 54 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 251 (Polychromatic418967fa.accept_13_12_2_4_1_3131 51 54 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 54 251 (accept_3_2 49 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  54 251 (Polychromatic418967fa.accept_14_6_12_13_1_3180 48 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 54 251 (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 251 (accept_3_2 46 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 54 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 251
  (Polychromatic418967fa.accept_13_5_2_4_1_3955 44 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 251 (accept_3_2 43 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  54 251 (Polychromatic418967fa.accept_17_8_3_13_1_5372 42 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 54 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 251 (accept_3_2 40 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 54 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 54 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 251
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 38 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 251 (accept_3_2 37 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  54 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 54 251 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 251 (accept_3_2 34 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 251 (accept_3_2 31 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  54 251 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 54 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 251 (accept_3_2 28 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 251 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 54 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 251
  (Polychromatic418967fa.accept_19_7_16_4_1_9861 26 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 251 (accept_3_2 25 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  54 251 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 251 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 251 (accept_3_2 22 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 251
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 20 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 251 (accept_3_2 19 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 251 (accept_3_2 16 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 54 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 251
  (Polychromatic418967fa.accept_25_14_4_1_1_15117 14 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 251 (accept_3_2 13 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 251 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 251 (accept_3_2 10 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 251 (accept_3_2 7 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  251 (Polychromatic418967fa.accept_13_6_2_4_1_923 6 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 251 (accept_3_2 4 54 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 251 (Polychromatic418967fa.accept_16_3_6_11_1_2718 3 54 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 251 (Polychromatic418967fa.accept_15_2_9_11_1_1551
  2 54 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 251 (accept_3_2 1 54
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 251))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 251 (allA_succ_of_accept 52 53 251 (accept_3_2 52 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 53 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 251 (accept_3_2 49 53 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 251 (Polychromatic418967fa.accept_10_8_3_1_1_1316
  48 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 251 (accept_3_2 46 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 251 (accept_3_2 43 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 251
  (Polychromatic418967fa.accept_16_9_5_11_1_3776 41 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 251 (accept_3_2 40 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 251 (Polychromatic418967fa.accept_16_7_5_11_1_4777 39 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 251 (accept_3_2 37 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 251 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 53 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 251
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 251 (accept_3_2 34 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 251 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 251 (accept_3_2 31 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 251
  (Polychromatic418967fa.accept_13_3_1_4_1_945 29 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 251 (accept_3_2 28 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 251 (Polychromatic418967fa.accept_15_12_8_11_1_4383 27 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 251 (accept_3_2 25 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 251 (accept_3_2 22 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 251 (Polychromatic418967fa.accept_27_21_26_8_1_13321 21 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 251 (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 53 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 251 (accept_3_2 19 53 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 251 (accept_3_2 16 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 251 (Polychromatic418967fa.accept_17_15_2_13_1_4153 15 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 251 (accept_3_2 13 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 251
  (Polychromatic418967fa.accept_19_11_15_4_1_7010 11 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 251 (accept_3_2 10 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 251 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 251 (accept_3_2 7 53 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 251 (accept_3_2 4 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  251 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 53 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 251 (accept_3_2 1 53 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 251))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 251 (allA_of_3_0 52 52
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 251 (allA_succ_of_accept 50 51 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 251 (accept_3_2 49 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 251 (accept_3_2 46 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 51 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 251 (accept_3_2 43 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 251 (Polychromatic418967fa.accept_13_3_12_4_1_110 42 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 251 (accept_3_2 40 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 251 (accept_3_2 37 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 251 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 251 (accept_3_2 34 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 51 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 251 (accept_3_2 31 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 251 (accept_3_2 28 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 251 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 51 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 251 (accept_3_2 25 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 251 (accept_3_2 22 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 251 (accept_3_2 19 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 251 (accept_3_2 16 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 251 (accept_3_2 13 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 251 (accept_3_2 10 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 51 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 251 (accept_3_2 7 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  251 (Polychromatic418967fa.accept_16_6_3_11_1_3751 6 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 51 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 251 (accept_3_2 4 51 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 251 (accept_3_2 1 51 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  251))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 251 (allA_succ_of_accept 49 50 251 (accept_3_2 49
  50 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 251
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 251 (accept_3_2 46 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 44
  50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 251 (accept_3_2 43 50
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 251
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 251 (accept_3_2 40 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 38
  50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 251 (accept_3_2 37 50
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 251
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 251 (Polychromatic418967fa.accept_14_7_8_13_1_3161 35 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 251 (accept_3_2 34 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 251 (Polychromatic418967fa.accept_12_8_2_11_1_246
  32 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 251 (accept_3_2 31
  50 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 50 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 50 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 251 (accept_3_2 28 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 50 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 50 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 26
  50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 50 251 (accept_3_2 25 50
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 50 251
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 50 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 251 (accept_3_2 22 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 50 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 20
  50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 50 251 (accept_3_2 19 50
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 251
  (Polychromatic418967fa.accept_24_18_2_11_1_11843 18 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 251 (accept_3_2 16 50 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 50 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 251
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 251 (accept_3_2 13 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 50 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 251 (accept_3_2 10 50 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 251 (accept_3_2 7 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 251 (accept_3_2 4 50 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 50 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  50 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 251 (accept_3_2 1 50 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 251)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 251 (allA_of_3_0 49 49 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 251 (allA_succ_of_accept 47 48
  251 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 251 (accept_3_2 46 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 251 (Polychromatic418967fa.accept_13_6_9_4_1_2288 45 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 251 (Polychromatic418967fa.accept_13_5_9_4_1_441 44 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 251 (accept_3_2 43 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 48 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 251 (accept_3_2 40 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 251 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 251 (accept_3_2 37 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 251 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 48 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 251
  (Polychromatic418967fa.accept_11_2_4_9_1_484 35 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 251 (accept_3_2 34 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 251 (accept_3_2 31 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 251 (Polychromatic418967fa.accept_21_9_6_20_1_1903 30 48 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 251 (accept_3_2 28 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 251 (Polychromatic418967fa.accept_17_10_14_13_1_12880 27 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 251 (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 48 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 251 (accept_3_2 25 48 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 48 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 251 (accept_3_2 22 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 251 (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 251 (accept_3_2 19 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 251 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 48 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 251
  (Polychromatic418967fa.accept_19_17_10_4_1_7032 17 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 251 (accept_3_2 16 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 251 (accept_3_2 13 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 251 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 48 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 251 (accept_3_2 10 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 251 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 251 (Polychromatic418967fa.accept_13_8_9_4_1_1552 8 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 251 (accept_3_2 7 48 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 48 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 251 (accept_3_2 4 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  251 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 48 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 48 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 251 (accept_3_2 1 48 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 251)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 251 (allA_succ_of_accept 46
  47 251 (accept_3_2 46 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 251
  (Polychromatic418967fa.accept_22_1_3_9_1_9082 45 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 251 (accept_3_2 43 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 41
  47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 251 (accept_3_2 40 47
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 251 (Polychromatic418967fa.accept_13_12_8_4_1_3099 38 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 251 (accept_3_2 37 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 251 (Polychromatic418967fa.accept_13_9_8_4_1_937
  35 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 251 (accept_3_2 34
  47 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 251
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 251 (accept_3_2 31 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 47 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 251 (accept_3_2 28 47
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 251
  (Polychromatic418967fa.accept_19_8_9_4_1_5593 27 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 251 (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 251 (accept_3_2 25 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 251 (accept_3_2 22 47
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 251
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 251 (accept_3_2 19 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 251 (Polychromatic418967fa.accept_11_6_3_9_1_906
  17 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 251 (accept_3_2 16
  47 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 251 (accept_3_2 13 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 11
  47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 251 (accept_3_2 10 47
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 251
  (Polychromatic418967fa.accept_13_9_8_4_1_937 9 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 251 (accept_3_2 7 47 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 47 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 5
  47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 251 (accept_3_2 4 47 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 251
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 2 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 251 (accept_3_2 1 47 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  251))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 251 (allA_of_3_0 46 46 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 45 251 (allA_succ_of_accept 44 45 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 251 (accept_3_2 43 45 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 251
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 41 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 251 (accept_3_2 40 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  45 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 45 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 251 (accept_3_2 37 45 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 251 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 45 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 251
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 35 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 251 (accept_3_2 34 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  45 251 (Polychromatic418967fa.accept_13_7_6_4_1_933 33 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 45 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 251 (accept_3_2 31 45 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 251
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 251 (accept_3_2 28 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  45 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 45 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 251 (accept_3_2 25 45 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 251 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 251 (accept_3_2 22 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  45 251 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 45 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 251 (accept_3_2 19 45 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 251
  (Polychromatic418967fa.accept_20_17_5_11_1_9622 17 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 251 (accept_3_2 16 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  45 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 45 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 251 (accept_3_2 13 45 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 251 (Polychromatic418967fa.accept_17_12_11_13_1_5378 12 45 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 45 251 (accept_3_2 10 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  45 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 251 (accept_3_2 7 45 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 251 (Polychromatic418967fa.accept_13_5_6_4_1_1582 5
  45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 251 (accept_3_2 4 45 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 3
  45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 251 (accept_3_2 1 45 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  251))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 251 (allA_succ_of_accept 43 44 251 (accept_3_2 43 44
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 251
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 42 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 251 (Polychromatic418967fa.accept_13_2_5_4_1_3926 41 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 251 (accept_3_2 40 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 251
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 251 (accept_3_2 37 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 251 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 251 (accept_3_2 34 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 251 (accept_3_2 31 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 251 (Polychromatic418967fa.accept_20_10_4_11_1_9652 30 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 251 (accept_3_2 28 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 251 (accept_3_2 25 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 251 (accept_3_2 22 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 251
  (Polychromatic418967fa.accept_16_4_12_11_1_2650 20 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 251 (accept_3_2 19 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 251 (accept_3_2 16 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 251 (accept_3_2 13 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 251 (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 251 (accept_3_2 10 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 251 (accept_3_2 7 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  251 (Polychromatic418967fa.accept_13_6_5_4_1_3924 6 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 44 251 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 251 (accept_3_2 4 44 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 44 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 44 251 (accept_3_2 1 44 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  251)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 251 (allA_of_3_0 43 43 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 42 251 (allA_succ_of_accept 41 42 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 251 (accept_3_2 40 42 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 39
  42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 251 (accept_3_2 37 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  42 251 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 42 251 (Polychromatic418967fa.accept_23_12_19_21_1_15116 35 42 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 251 (accept_3_2 34 42 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 251 (accept_3_2 31 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  42 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 42 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 251 (accept_3_2 28 42 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 42 251 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 42 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 251
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 42 251 (accept_3_2 25 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  42 251 (Polychromatic418967fa.accept_25_24_17_1_1_15115 24 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 42 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 251 (accept_3_2 22 42 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 42 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 251 (accept_3_2 19 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  42 251 (Polychromatic418967fa.accept_22_18_20_9_1_13659 18 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 42 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 251 (accept_3_2 16 42 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 251 (Polychromatic418967fa.accept_16_15_10_11_1_1727 15 42 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 251 (accept_3_2 13 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  42 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 42 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 251 (accept_3_2 10 42 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 42 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 251
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 8 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 42 251 (accept_3_2 7 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42
  251 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 251 (accept_3_2 4 42 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 42 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 42 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  42 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 251 (accept_3_2 1 42 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 251)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 251
  (allA_succ_of_accept 40 41 251 (accept_3_2 40 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 251 (accept_3_2 37 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 251 (Polychromatic418967fa.accept_16_4_9_11_1_7159 36 41 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 251
  (Polychromatic418967fa.accept_19_16_3_4_1_4281 35 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 251 (accept_3_2 34 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 251 (Polychromatic418967fa.accept_11_10_8_9_1_492 32 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 251 (accept_3_2 31 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 251 (accept_3_2 28 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 251 (Polychromatic418967fa.accept_19_8_3_4_1_9865 27 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 251 (accept_3_2 25 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 251
  (Polychromatic418967fa.accept_17_6_7_13_1_3062 23 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 251 (accept_3_2 22 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 251 (accept_3_2 19 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 251
  (Polychromatic418967fa.accept_20_17_1_11_1_6555 17 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 251 (accept_3_2 16 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 251 (accept_3_2 13 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 251 (accept_3_2 10 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 251 (Polychromatic418967fa.accept_24_9_17_11_1_4810 9 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 251 (Polychromatic418967fa.accept_18_8_5_17_1_1388 8 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 251 (accept_3_2 7 41 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 251
  (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 251 (accept_3_2 4 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  251 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 41 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 251 (accept_3_2 1 41 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 251))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 251 (allA_of_3_0 40 40 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 251 (allA_succ_of_accept 38 39 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 251 (accept_3_2 37 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 39 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 251 (accept_3_2 34 39 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 39 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 251 (accept_3_2 31 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 39 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 251 (accept_3_2 28 39 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 251 (Polychromatic418967fa.accept_17_10_5_13_1_12853 27 39 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 251 (accept_3_2 25 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 39 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 251 (accept_3_2 22 39 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 39 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 251 (accept_3_2 19 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 251 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 39 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 251 (accept_3_2 16 39 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 251 (accept_3_2 13 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 39 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 251 (accept_3_2 10 39 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 39 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 251 (accept_3_2 7 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 39 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 39 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 251 (accept_3_2 4 39 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 251 (accept_3_2 1 39 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 251))))))))))))))))))))))))))))))))))))))) (allB_succ 38 251
  (allA_succ_of_accept 37 38 251 (accept_3_2 37 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 251 (Polychromatic418967fa.accept_16_4_6_11_1_3753 36 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 251 (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 38 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 251 (accept_3_2 34 38 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 251 (accept_3_2 31 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 251 (accept_3_2 28 38 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 251
  (Polychromatic418967fa.accept_17_9_4_13_1_3057 26 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 251 (accept_3_2 25 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 38 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 251 (accept_3_2 22 38 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 251 (accept_3_2 19 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 251 (accept_3_2 16 38 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 251 (accept_3_2 13 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 38 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 251 (accept_3_2 10 38 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 251
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 251 (accept_3_2 7 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 38 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 251 (accept_3_2 4 38 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 38
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 251 (accept_3_2 1 38 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 251)))))))))))))))))))))))))))))))))))))) (allB_succ 37 251
  (allA_of_3_0 37 37 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 251 (allA_succ_of_accept 35 36 251
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 251 (accept_3_2 34 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 251 (accept_3_2 31 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 36 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 251
  (Polychromatic418967fa.accept_19_10_17_4_1_4227 29 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 251 (accept_3_2 28 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 251 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 251 (accept_3_2 25 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 251 (Polychromatic418967fa.accept_13_11_10_4_1_1565 24 36 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 251 (accept_3_2 22 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 251 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 251 (Polychromatic418967fa.accept_13_7_10_4_1_919 20 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 251 (accept_3_2 19 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 251 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 36 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 251
  (Polychromatic418967fa.accept_10_7_6_1_1_486 17 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 251 (accept_3_2 16 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 251 (Polychromatic418967fa.accept_13_1_10_4_1_954 14 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 251 (accept_3_2 13 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 36 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 251
  (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 251 (accept_3_2 10 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 251 (Polychromatic418967fa.accept_13_8_10_4_1_2270 8 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 251 (accept_3_2 7 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 251 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 36 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 251
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 251 (accept_3_2 4 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  251 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 36 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 36 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 251 (accept_3_2 1 36 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 36 251)))))))))))))))))))))))))))))))))))) (allB_succ 35 251 (allA_succ_of_accept 34 35
  251 (accept_3_2 34 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 251
  (Polychromatic418967fa.accept_13_7_9_4_1_918 33 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 251 (Polychromatic418967fa.accept_13_6_9_4_1_2288 32 35 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 251 (accept_3_2 31 35 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 251 (Polychromatic418967fa.accept_16_14_3_11_1_5969 30 35 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 251
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 251 (accept_3_2 28 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 251 (Polychromatic418967fa.accept_21_6_14_20_1_4594 27 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 251 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 35 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 251 (accept_3_2 25 35 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 251 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 35 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 251
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 251 (accept_3_2 22 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 251 (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 251 (Polychromatic418967fa.accept_13_7_9_4_1_918 20 35 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 251 (accept_3_2 19 35 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 251 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 35 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 251
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 251 (accept_3_2 16 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 251 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 251 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 35 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 251 (accept_3_2 13 35 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 251 (Polychromatic418967fa.accept_17_12_1_13_1_6672 12 35 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 251
  (Polychromatic418967fa.accept_19_11_16_4_1_7075 11 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 251 (accept_3_2 10 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 251 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 251 (Polychromatic418967fa.accept_13_8_9_4_1_1552 8 35 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 251 (accept_3_2 7 35 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 251 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 35 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 251
  (Polychromatic418967fa.accept_13_5_9_4_1_441 5 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 251 (accept_3_2 4 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  251 (Polychromatic418967fa.accept_19_3_16_4_1_7076 3 35 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 35 251 (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 35 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 251 (accept_3_2 1 35 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 35 251))))))))))))))))))))))))))))))))))) (allB_succ 34 251 (allA_of_3_0 34 34 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 251 (allA_succ_of_accept 32 33 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 251 (accept_3_2 31 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 33 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 251 (accept_3_2 28 33 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 33 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 251 (accept_3_2 25 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 251 (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 33 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 251 (accept_3_2 22 33 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 251 (accept_3_2 19 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 251 (Polychromatic418967fa.accept_22_17_11_9_1_10636 17 33 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 251 (accept_3_2 16 33 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 33 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 251 (accept_3_2 13 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 33 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 251 (accept_3_2 10 33 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 251 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 33 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 251 (accept_3_2 7 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 33 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 251 (accept_3_2 4 33 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 251 (accept_3_2 1 33 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 251))))))))))))))))))))))))))))))))) (allB_succ 32 251
  (allA_succ_of_accept 31 32 251 (accept_3_2 31 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  32 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 32 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 251 (accept_3_2 28 32 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 251 (accept_3_2 25 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 32 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 251 (accept_3_2 22 32 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 251 (accept_3_2 19 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 251 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 32 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 251 (accept_3_2 16 32 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 251
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 251 (accept_3_2 13 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 251 (accept_3_2 10 32 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 251
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 251 (accept_3_2 7 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 32 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 32 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 251 (accept_3_2 4 32 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  32 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 251 (accept_3_2 1 32 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 251)))))))))))))))))))))))))))))))) (allB_succ 31 251
  (allA_of_3_0 31 31 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 251 (allA_succ_of_accept 29 30 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 251 (accept_3_2 28 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 251 (Polychromatic418967fa.accept_18_9_12_17_1_6060 27 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 251 (Polychromatic418967fa.accept_19_7_11_4_1_1872 26 30 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 251 (accept_3_2 25 30 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 30 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 251 (accept_3_2 22 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 30 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 251 (accept_3_2 19 30 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 30 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 251 (accept_3_2 16 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 30 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 251 (accept_3_2 13 30 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 251 (Polychromatic418967fa.accept_19_12_11_4_1_1844 12 30 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 251 (accept_3_2 10 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 30 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 251 (accept_3_2 7 30 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 30 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 30 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 251 (accept_3_2 4 30 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 30
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 251 (accept_3_2 1 30 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  251)))))))))))))))))))))))))))))) (allB_succ 29 251 (allA_succ_of_accept 28 29 251 (accept_3_2 28 29 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 251 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 29 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 251 (accept_3_2 25 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 29 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 251 (accept_3_2 22 29 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 29 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 251
  (Polychromatic418967fa.accept_13_7_3_4_1_459 20 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 251 (accept_3_2 19 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 251 (Polychromatic418967fa.accept_19_17_10_4_1_7032 17 29 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 251 (accept_3_2 16 29 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 29 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 251 (accept_3_2 13 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 251 (Polychromatic418967fa.accept_17_11_12_13_1_3030 11 29 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 251 (accept_3_2 10 29 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 29 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 251
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 251 (accept_3_2 7 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 251 (accept_3_2 4 29 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 29 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 251 (accept_3_2 1 29 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 251))))))))))))))))))))))))))))) (allB_succ 28 251 (allA_of_3_0
  28 28 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 251 (allA_succ_of_accept 26 27 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 251 (accept_3_2 25 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 251 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 251 (Polychromatic418967fa.accept_13_10_1_4_1_3103 23 27 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 251 (accept_3_2 22 27 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 251 (accept_3_2 19 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 251 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 251 (Polychromatic418967fa.accept_19_17_8_4_1_4212 17 27 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 251 (accept_3_2 16 27 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 251 (Polychromatic418967fa.accept_18_15_9_17_1_6043 15 27
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 251 (accept_3_2 13 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 251 (Polychromatic418967fa.accept_18_12_9_17_1_7428 12 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 251 (Polychromatic418967fa.accept_21_11_6_20_1_4589 11 27 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 251 (accept_3_2 10 27 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 27 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 251 (accept_3_2 7 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  251 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 27 251 (Polychromatic418967fa.accept_13_5_1_4_1_3966 5 27 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 251 (accept_3_2 4 27 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 251 (Polychromatic418967fa.accept_13_3_1_4_1_945 3 27 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 251 (accept_3_2 1 27 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27
  251))))))))))))))))))))))))))) (allB_succ 26 251 (allA_succ_of_accept 25 26 251 (accept_3_2 25 26 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 251 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 26 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 251
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 23 26 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 251 (accept_3_2 22 26 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  26 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 26 251 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 26 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 251 (accept_3_2 19 26 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 26 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 251 (accept_3_2 16 26 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  26 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 26 251 (Polychromatic418967fa.accept_19_14_7_4_1_4210 14 26 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 251 (accept_3_2 13 26 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 26 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 26 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 251 (accept_3_2 10 26 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 26 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 251 (accept_3_2 7 26 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 251 (Polychromatic418967fa.accept_14_6_12_13_1_3180 6 26 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 251 (accept_3_2 4 26 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 251
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 26 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 251 (accept_3_2 1 26 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  251)))))))))))))))))))))))))) (allB_succ 25 251 (allA_of_3_0 25 25 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 251 (allA_succ_of_accept 23 24 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 251 (accept_3_2 22 24 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 24 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 251 (accept_3_2 19 24 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 24 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 251 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 24 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 251 (accept_3_2 16 24 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 251 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 24 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 24 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 251 (accept_3_2 13 24 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 24 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 251 (accept_3_2 10 24 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 251
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 8 24 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 251 (accept_3_2 7 24 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  251 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 24 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 24 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 251 (accept_3_2 4 24 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 24 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 251 (accept_3_2 1 24 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  251)))))))))))))))))))))))) (allB_succ 23 251 (allA_succ_of_accept 22 23 251 (accept_3_2 22 23 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 23 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 251
  (Polychromatic418967fa.accept_8_4_7_3_1_144 20 23 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 251 (accept_3_2 19 23 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 23 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 251 (accept_3_2 16 23 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 23 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 251
  (Polychromatic418967fa.accept_13_1_10_4_1_954 14 23 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 251 (accept_3_2 13 23 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 23 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 251 (accept_3_2 10 23 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 251 (Polychromatic418967fa.accept_21_9_2_20_1_857 9 23 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 23 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 251 (accept_3_2 7 23 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 23 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 251 (Polychromatic418967fa.accept_13_5_10_4_1_1564 5 23 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 251 (accept_3_2 4 23 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 23 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 251 (accept_3_2 1 23 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 251))))))))))))))))))))))) (allB_succ 22 251 (allA_of_3_0 22 22
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 251 (allA_succ_of_accept 20 21 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 251 (accept_3_2 19 21 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 251 (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 21 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 251 (accept_3_2 16 21 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 251 (accept_3_2 13 21 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 251 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 21 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 21 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 251 (accept_3_2 10 21 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 251 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 21 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 251 (accept_3_2 7 21 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 21 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 251 (accept_3_2 4 21 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 251 (accept_3_2 1 21 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 251))))))))))))))))))))) (allB_succ 20 251 (allA_succ_of_accept
  19 20 251 (accept_3_2 19 20 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 251
  (Polychromatic418967fa.accept_22_18_20_9_1_13659 18 20 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 251 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 20 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 251 (accept_3_2 16 20 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 20 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 20 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 20 251 (accept_3_2 13 20 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  20 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 20 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 20 251 (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 20 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 251 (accept_3_2 10 20 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 251
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 20 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 251 (accept_3_2 7 20 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20
  251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 20 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 20 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 251 (accept_3_2 4 20 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 251 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  20 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 251 (accept_3_2 1 20 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 251)))))))))))))))))))) (allB_succ 19 251 (allA_of_3_0 19 19 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 18 251 (allA_succ_of_accept 17 18 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 18 251 (accept_3_2 16 18 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  18 251 (Polychromatic418967fa.accept_13_2_5_4_1_3926 15 18 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 18 251 (Polychromatic418967fa.accept_13_1_5_4_1_463 14 18 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 251 (accept_3_2 13 18 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 18 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 251
  (Polychromatic418967fa.accept_19_11_18_4_1_2957 11 18 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 18 251 (accept_3_2 10 18 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  18 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 18 251 (Polychromatic418967fa.accept_15_8_3_11_1_849 8 18 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 251 (accept_3_2 7 18 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 18 251 (Polychromatic418967fa.accept_13_6_5_4_1_3924 6 18 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 251 (accept_3_2 4 18 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  18 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 18 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 18 251 (accept_3_2 1 18 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  251)))))))))))))))))) (allB_succ 17 251 (allA_succ_of_accept 16 17 251 (accept_3_2 16 17 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 251 (Polychromatic418967fa.accept_16_15_1_11_1_3747 15 17 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 251 (accept_3_2 13 17 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 251 (Polychromatic418967fa.accept_16_12_1_11_1_5958 12 17 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 17 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 251 (accept_3_2 10 17 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 17 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 251
  (Polychromatic418967fa.accept_19_8_17_4_1_886 8 17 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 251 (accept_3_2 7 17 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 251 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 17 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 251 (accept_3_2 4 17 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 251 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 17 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 251 (accept_3_2 1 17 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 251))))))))))))))))) (allB_succ 16 251 (allA_of_3_0 16 16 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 251 (allA_succ_of_accept 14 15 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 251 (accept_3_2 13 15 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 15 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 251 (accept_3_2 10 15 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 15 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 251 (accept_3_2 7 15 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  251 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 15 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 15 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 251 (accept_3_2 4 15 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 15 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 251 (accept_3_2 1 15 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 251))))))))))))))) (allB_succ 14 251 (allA_succ_of_accept 13 14
  251 (accept_3_2 13 14 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 251
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 14 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 14 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 251 (accept_3_2 10 14 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 251 (Polychromatic418967fa.accept_12_8_2_11_1_246 8
  14 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 251 (accept_3_2 7 14 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6
  14 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 251 (accept_3_2 4 14 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 14 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 251 (accept_3_2 1 14 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 251)))))))))))))) (allB_succ 13 251 (allA_of_3_0 13 13 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 251 (allA_succ_of_accept 11 12 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 251 (accept_3_2 10 12 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 251 (Polychromatic418967fa.accept_10_9_2_1_1_840 9
  12 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 12 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 251 (accept_3_2 7 12 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 12 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 251 (accept_3_2 4 12 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 251 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 12 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  12 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 251 (accept_3_2 1 12 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 251)))))))))))) (allB_succ 11 251 (allA_succ_of_accept 10 11 251
  (accept_3_2 10 11 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 11 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 251 (Polychromatic418967fa.accept_13_8_11_4_1_1553 8 11 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 251 (accept_3_2 7 11 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 11 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  11 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 251 (accept_3_2 4 11 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  11 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 11 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 251 (accept_3_2 1 11 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  251))))))))))) (allB_succ 10 251 (allA_of_3_0 10 10 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 251
  (allA_succ_of_accept 8 9 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 251 (accept_3_2 7 9 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 9
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 251 (accept_3_2 4 9 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 9
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 251 (accept_3_2 1 9 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 251)))))))))
  (allB_succ 8 251 (allA_succ_of_accept 7 8 251 (accept_3_2 7 8 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 251 (Polychromatic418967fa.accept_22_6_8_9_1_15114 6 8 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 8 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 251 (accept_3_2 4 8 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 8 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 251 (accept_3_2 1 8 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 251))))))))
  (allB_succ 7 251 (allA_of_3_0 7 7 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 251 (allA_succ_of_accept 5
  6 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 251 (accept_3_2 4 6 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 251
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 6 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 6 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 251 (accept_3_2 1 6 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 251)))))) (allB_succ 5 251 (allA_succ_of_accept 4 5 251 (accept_3_2 4 5 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 5 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 251 (accept_3_2 1 5 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 251)))))
  (allB_succ 4 251 (allA_of_3_0 4 4 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 251 (allA_succ_of_accept 2
  3 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 251 (accept_3_2 1 3 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 251)))
  (allB_succ 2 251 (allA_succ_of_accept 1 2 251 (accept_3_2 1 2 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  251)) (allB_two
  251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


