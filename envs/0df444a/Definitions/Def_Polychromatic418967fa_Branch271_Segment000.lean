-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch271_Segment000
-- name    : Polychromatic418967fa_Branch271_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:49:01.369415+00:00
-- url     : https://prove2.me/theorems/663cb999-b117-4410-ae8a-9789123d871e
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

def Polychromatic418967fa.branch_271_segment_000 : allB 123 271 :=
  allB_succ 122 271 (allA_of_3_1 122 122 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 121 271
  (allA_succ_of_accept 120 121 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 120 121 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 271 (accept_3_3 119 121 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 121 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 271
  (Polychromatic418967fa.accept_19_3_7_5_1_12632 117 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 121 271 (accept_3_3 116 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 121 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 115 121 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 121 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 121
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 271 (accept_3_3 113 121
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 271
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 112 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 121 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 111 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 121 271 (accept_3_3 110 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 121 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 109 121
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 121 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 108 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 121 271 (accept_3_3 107 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 121 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 121 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 105 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 121 271 (accept_3_3 104 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 121 271 (Polychromatic418967fa.accept_13_12_4_11_1_1925 103
  121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 121 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 121 271 (accept_3_3 101 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 121 271 (Polychromatic418967fa.accept_18_10_13_1_1_7736 100 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 271 (Polychromatic418967fa.accept_13_8_4_11_1_3469 99 121 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 121 271 (accept_3_3 98 121 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 121 271 (Polychromatic418967fa.accept_9_7_4_1_1_391
  97 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 121 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 96 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 121 271 (accept_3_3 95 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 121 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 121 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 93 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 121 271 (accept_3_3 92 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 121 271 (Polychromatic418967fa.accept_14_7_9_5_1_529 91 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 121 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 121 271 (accept_3_3 89 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 121 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 121 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 87 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 121 271 (accept_3_3 86 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 121 271 (Polychromatic418967fa.accept_13_7_4_11_1_1967 85 121 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 121 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 121 271 (accept_3_3 83 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 121 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 121 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 121 271 (accept_3_3 80 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 121 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 121 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 121 271 (accept_3_3 77 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 121 271 (Polychromatic418967fa.accept_17_8_2_16_1_5598 76 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 121 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 121 271 (accept_3_3 74 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 121 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 121 271
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 72 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 121 271 (accept_3_3 71 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 121 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 121 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 121 271 (accept_3_3 68 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 121 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 121 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 121 271 (accept_3_3 65 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 121 271 (Polychromatic418967fa.accept_13_12_4_11_1_1925 64 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 121 271 (Polychromatic418967fa.accept_14_7_9_5_1_529 63 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 271 (accept_3_3 62 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 121 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 121 271 (accept_3_3 59 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 121 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 121 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 271 (accept_3_3 56 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 121 271 (Polychromatic418967fa.accept_19_17_7_5_1_1883 55 121 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 121 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 121 271 (accept_3_3 53 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 121 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 121 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 271 (accept_3_3 50 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 271 (Polychromatic418967fa.accept_13_10_4_11_1_1969 49 121 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 121 271 (accept_3_3 47 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 121 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 121 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 271 (accept_3_3 44 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 121 271 (accept_3_3 41 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 121 271 (Polychromatic418967fa.accept_16_8_9_15_1_5112 40 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 271 (accept_3_3 38 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 271 (Polychromatic418967fa.accept_20_17_1_11_1_6555 37 121 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 271
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 121 271 (accept_3_3 35 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 121 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 121 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 271 (accept_3_3 32 121 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 271 (Polychromatic418967fa.accept_7_3_2_5_1_147
  31 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 121 271 (accept_3_3 29 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 121 271 (Polychromatic418967fa.accept_13_2_4_11_1_2003 28 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 121 271 (Polychromatic418967fa.accept_20_7_1_11_1_3766 27 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 271 (accept_3_3 26 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 121 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 271 (accept_3_3 23 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 271 (accept_3_3 20 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 271 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 271 (accept_3_3 17 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 271 (accept_3_3 14 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 271 (Polychromatic418967fa.accept_19_13_7_5_1_5712 13 121 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 271 (accept_3_3 11 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 271 (Polychromatic418967fa.accept_19_9_7_5_1_9887 9 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 271 (accept_3_3 8 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 271 (accept_3_3 5 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 121 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 271 (accept_3_3 2 121 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 271 (Polychromatic418967fa.accept_17_1_2_16_1_5596 1 121 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 271 (allA_succ_of_accept 119 120 271 (accept_3_3 119 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 120 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 118 120 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 120 271 (Polychromatic418967fa.accept_17_15_1_16_1_8166 117
  120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 271 (accept_3_3 116
  120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 120 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 115 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 120 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 114 120 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 120 271 (accept_3_3 113 120 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 120 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 112 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 111 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 120 271 (accept_3_3 110 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 120 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 109 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 120 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 108 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 271 (accept_3_3 107 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 106 120
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 120 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 105 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 120 271 (accept_3_3 104 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 120 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 103 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 120 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 102 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 120 271 (accept_3_3 101 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 271 (Polychromatic418967fa.accept_16_4_8_15_1_1113 100
  120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 271
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 99 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 120 271 (accept_3_3 98 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 120 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 97 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 120 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 96 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 120 271 (accept_3_3 95 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 94 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 271
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 93 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 120 271 (accept_3_3 92 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 120 271 (Polychromatic418967fa.accept_11_3_10_7_1_129 91 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 120 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 120 271 (accept_3_3 89 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 88 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 87 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 120 271 (accept_3_3 86 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 120 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 85 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 120 271 (Polychromatic418967fa.accept_16_4_8_15_1_1113 84 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 120 271 (accept_3_3 83 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 271 (Polychromatic418967fa.accept_22_16_10_7_1_5554 82 120
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 81 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 120 271 (accept_3_3 80 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 120 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 120 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 78 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 271 (accept_3_3 77 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 271
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 75 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 120 271 (accept_3_3 74 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 120 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 120 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 120 271 (Polychromatic418967fa.accept_13_7_3_11_1_280 72 120
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 120 271 (accept_3_3 71 120
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 271
  (Polychromatic418967fa.accept_9_7_3_1_1_386 70 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 120 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 120 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 271 (accept_3_3 68 120 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 120 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 120 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 66
  120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 120 271 (accept_3_3 65
  120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 271
  (Polychromatic418967fa.accept_19_7_6_5_1_4320 64 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 120 271 (Polychromatic418967fa.accept_17_12_1_16_1_4360 63 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 271 (accept_3_3 62 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 120 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 120 271 (accept_3_3 59 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 120 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 120 271 (Polychromatic418967fa.accept_13_5_3_11_1_1288 57 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 271 (accept_3_3 56 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 120 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 120 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 120 271
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 120 271 (accept_3_3 53 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 120 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 120 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 271 (accept_3_3 50 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 120 271 (accept_3_3 47 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 120 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 120 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 271 (accept_3_3 44 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 120 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 120 271 (accept_3_3 41 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 120 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 120 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 271 (accept_3_3 38 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 271 (Polychromatic418967fa.accept_19_18_6_5_1_4321 37 120 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 271
  (Polychromatic418967fa.accept_11_3_10_7_1_129 36 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 120 271 (accept_3_3 35 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 120 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 120 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 271 (accept_3_3 32 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 271
  (Polychromatic418967fa.accept_19_11_6_5_1_11299 30 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 120 271 (accept_3_3 29 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 120 271 (Polychromatic418967fa.accept_13_2_3_11_1_1287 28 120 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 120 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 271 (accept_3_3 26 120 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 271 (Polychromatic418967fa.accept_7_4_1_5_1_540
  25 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 120 271 (accept_3_3 23 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 120 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 120 271 (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 271 (accept_3_3 20 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 271 (Polychromatic418967fa.accept_17_2_1_16_1_6946 19 120
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 120 271 (accept_3_3 17 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 120 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 120 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 271 (accept_3_3 14 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 271
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 12 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 120 271 (accept_3_3 11 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 120 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 271 (Polychromatic418967fa.accept_16_9_8_15_1_5095 9 120
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 271 (accept_3_3 8 120 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 120 271 (accept_3_3 5 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  120 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 120 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 120 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 271 (accept_3_3 2 120 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 271 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 120 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 271 (allA_of_3_1 119 119 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 118 271
  (allA_succ_of_accept 117 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 118 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 118 271 (accept_3_3 116 118 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 118 271 (Polychromatic418967fa.accept_15_10_13_1_1_3698 115 118 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 118 271
  (Polychromatic418967fa.accept_11_4_8_7_1_819 114 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 118 271 (accept_3_3 113 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 118 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 112 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 118 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 118 271 (accept_3_3 110 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 109 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 118 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 118 271
  (Polychromatic418967fa.accept_15_3_13_1_1_479 108 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 118 271 (accept_3_3 107 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 118 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 106 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 118 271 (accept_3_3 104 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 118 271 (Polychromatic418967fa.accept_10_3_8_1_1_182 103 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 118 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 102 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 118 271 (accept_3_3 101 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 118 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 100 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 118 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 118 271 (accept_3_3 98 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 118 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 118 271
  (Polychromatic418967fa.accept_19_1_4_5_1_4313 96 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 118 271 (accept_3_3 95 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 118 271 (Polychromatic418967fa.accept_13_3_1_11_1_1268 94 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 118 271 (accept_3_3 92 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 118 271 (Polychromatic418967fa.accept_19_15_4_5_1_11338 91 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 118 271
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 90 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 118 271 (accept_3_3 89 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 118 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 118 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 118 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 118 271 (accept_3_3 86 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 85
  118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 118 271
  (Polychromatic418967fa.accept_19_8_4_5_1_8569 84 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 118 271 (accept_3_3 83 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 118 271 (Polychromatic418967fa.accept_19_6_4_5_1_5650 82 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 118 271 (accept_3_3 80 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 118 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 79 118 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 118 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 78 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 118 271 (accept_3_3 77 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 118 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 118 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 271 (accept_3_3 74 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 118 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 271
  (Polychromatic418967fa.accept_13_7_1_11_1_732 72 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 118 271 (accept_3_3 71 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 118 271 (Polychromatic418967fa.accept_11_4_8_7_1_819 70 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 271 (accept_3_3 68 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 118 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 271
  (Polychromatic418967fa.accept_19_9_4_5_1_3019 66 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 271 (accept_3_3 65 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 271 (accept_3_3 62 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 118 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 271 (accept_3_3 59 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 271 (Polychromatic418967fa.accept_19_1_4_5_1_4313 58 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 271 (accept_3_3 56 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 271 (Polychromatic418967fa.accept_13_3_1_11_1_1268 55 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 271
  (Polychromatic418967fa.accept_22_10_8_7_1_11977 54 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 118 271 (accept_3_3 53 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 118 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 118 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 118 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 271 (accept_3_3 50 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 271
  (Polychromatic418967fa.accept_11_4_8_7_1_819 48 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 271 (accept_3_3 47 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 271 (accept_3_3 44 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 118 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 271
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 42 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 271 (accept_3_3 41 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 271 (accept_3_3 38 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 271 (accept_3_3 35 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 271 (Polychromatic418967fa.accept_13_8_1_11_1_1284 34 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 271 (accept_3_3 32 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 271 (Polychromatic418967fa.accept_18_13_10_1_1_9025 31 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 271
  (Polychromatic418967fa.accept_25_5_18_21_1_16605 30 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 118 271 (accept_3_3 29 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 118 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 118 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 118 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 271 (accept_3_3 26 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 271
  (Polychromatic418967fa.accept_29_24_2_10_1_16604 24 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 118 271 (accept_3_3 23 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 118 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 118 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 271 (accept_3_3 20 118 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331
  19 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 271 (accept_3_3 17 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 271 (accept_3_3 14 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 271
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 118 271 (accept_3_3 11 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 118 271 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 271 (accept_3_3 8 118
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 271
  (Polychromatic418967fa.accept_13_7_1_11_1_732 7 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 118 271 (Polychromatic418967fa.accept_19_6_4_5_1_5650 6 118 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 271 (accept_3_3 5 118 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 118 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 118 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3
  118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 271 (accept_3_3 2 118
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 271 (Polychromatic418967fa.accept_4_1_2_3_1_9
  1 118 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 271 (allA_succ_of_accept 116 117 271 (accept_3_3 116 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 271 (Polychromatic418967fa.accept_19_1_3_5_1_3092 115 117 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27
  114 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 271 (accept_3_3
  113 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 271
  (Polychromatic418967fa.accept_6_4_3_1_1_57 112 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 117 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 111 117 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 271 (accept_3_3 110 117 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 117 271 (Polychromatic418967fa.accept_15_4_12_1_1_1081 109 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 271
  (Polychromatic418967fa.accept_20_8_17_11_1_9604 108 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 117 271 (accept_3_3 107 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 117 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 117 271 (Polychromatic418967fa.accept_19_10_3_5_1_11346 105
  117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 271 (accept_3_3 104
  117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 271
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 103 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 271 (accept_3_3 101 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 117
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 117 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 99 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 117 271 (accept_3_3 98 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 117 271 (Polychromatic418967fa.accept_16_1_5_15_1_2918 97 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 117 271 (Polychromatic418967fa.accept_10_6_7_1_1_1297 96 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 271 (accept_3_3 95 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 271
  (Polychromatic418967fa.accept_18_3_9_1_1_3690 93 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 117 271 (accept_3_3 92 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 117 271 (Polychromatic418967fa.accept_21_7_12_19_1_10712 91 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 271 (accept_3_3 89 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 87 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 117 271 (accept_3_3 86 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 117 271 (Polychromatic418967fa.accept_20_5_17_11_1_6571 85 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 117 271 (Polychromatic418967fa.accept_10_4_7_1_1_471 84 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 271 (accept_3_3 83 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 271
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 81 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 117 271 (accept_3_3 80 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 117 271 (Polychromatic418967fa.accept_15_4_12_1_1_1081 79 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 117 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 271 (accept_3_3 77 117 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 75 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 117 271 (accept_3_3 74 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 117 271 (Polychromatic418967fa.accept_15_13_12_1_1_1841 73 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 117 271 (Polychromatic418967fa.accept_17_4_15_16_1_3231 72 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 271 (accept_3_3 71 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 271
  (Polychromatic418967fa.accept_17_1_15_16_1_2202 69 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 271 (accept_3_3 68 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 271 (Polychromatic418967fa.accept_19_10_3_5_1_11346 67 117 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 271 (accept_3_3 65
  117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 271
  (Polychromatic418967fa.accept_6_4_3_1_1_57 64 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 117 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 117 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 271 (accept_3_3 62 117 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 117 271 (Polychromatic418967fa.accept_20_1_17_11_1_8119 61 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 271
  (Polychromatic418967fa.accept_18_6_9_1_1_3769 60 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 117 271 (accept_3_3 59 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 117 271 (Polychromatic418967fa.accept_18_3_9_1_1_3690 57 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 271 (accept_3_3 56 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 271 (Polychromatic418967fa.accept_17_4_15_16_1_3231 55 117
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 117 271 (accept_3_3 53 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 117 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 117 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 51 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 271 (accept_3_3 50 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 271 (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 117
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 271
  (Polychromatic418967fa.accept_17_14_15_16_1_1271 48 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 271 (accept_3_3 47 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 271 (Polychromatic418967fa.accept_17_11_15_16_1_4377 45
  117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 271 (accept_3_3 44
  117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 271
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 271 (accept_3_3 41 117 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 117 271 (accept_3_3 38 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 117 271 (Polychromatic418967fa.accept_24_13_21_7_1_4502 37 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 117 271 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 271 (accept_3_3 35 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 271
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 33 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 117 271 (accept_3_3 32 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 117 271 (Polychromatic418967fa.accept_17_14_15_16_1_1271 31 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 271 (accept_3_3 29 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 117 271 (accept_3_3 26 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 117 271 (Polychromatic418967fa.accept_19_6_3_5_1_9897 25 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 117 271 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 271 (accept_3_3 23 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 271
  (Polychromatic418967fa.accept_17_4_15_16_1_3231 21 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 271 (accept_3_3 20 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 271 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 117 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 271 (accept_3_3 17 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 271 (accept_3_3 14 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 117 271 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 271 (Polychromatic418967fa.accept_24_12_21_7_1_13288 12 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 271 (accept_3_3 11 117 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 271
  (Polychromatic418967fa.accept_21_9_12_19_1_12172 9 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 271 (accept_3_3 8 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 271 (Polychromatic418967fa.accept_19_7_3_5_1_8585 7 117 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 271 (accept_3_3 5 117 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4
  117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 271 (accept_3_3 2 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 271 (Polychromatic418967fa.accept_16_1_5_15_1_2918 1 117 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 271 (allA_of_3_1 116 116 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 271
  (allA_succ_of_accept 114 115 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 114 115 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 271 (accept_3_3 113 115 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 115 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 112 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 111 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 115 271 (accept_3_3 110 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 115 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 109 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 115 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 108 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 115 271 (accept_3_3 107 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 115 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 106 115
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 115 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 105 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 115 271 (accept_3_3 104 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 115 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 103 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 115 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 102 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 115 271 (accept_3_3 101 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 115 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 100 115
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 115 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 99 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 115 271 (accept_3_3 98 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 115 271 (Polychromatic418967fa.accept_11_9_5_7_1_815 97 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 115 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 96 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 115 271 (accept_3_3 95 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 115 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 94 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 93 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 115 271 (accept_3_3 92 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 115 271 (Polychromatic418967fa.accept_16_11_3_15_1_1989 91 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 115 271 (Polychromatic418967fa.accept_20_10_15_11_1_3759 90 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 115 271 (accept_3_3 89 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 271 (Polychromatic418967fa.accept_15_13_10_1_1_1862 88 115
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 87 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 271 (accept_3_3 86 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 115 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 115 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 271 (accept_3_3 83 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 271 (Polychromatic418967fa.accept_14_12_3_5_1_1868 82 115 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 271
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 115 271 (accept_3_3 80 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 115 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 79 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 115 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 271 (accept_3_3 77 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 115 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 76 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 75 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 115 271 (accept_3_3 74 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 115 271 (Polychromatic418967fa.accept_15_13_10_1_1_1862 73 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 115 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 271 (accept_3_3 71 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 115 271 (Polychromatic418967fa.accept_18_16_7_1_1_6332 70 115 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 115 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 69 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 271 (accept_3_3 68 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 271 (accept_3_3 65 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 115 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 271
  (Polychromatic418967fa.accept_17_12_13_16_1_3226 63 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 115 271 (accept_3_3 62 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 115 271 (Polychromatic418967fa.accept_16_13_3_15_1_1931 61 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 271 (Polychromatic418967fa.accept_8_4_3_7_1_491
  60 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 271 (accept_3_3 59
  115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 58 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 115 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 115 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 271 (accept_3_3 56 115 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 115 271 (Polychromatic418967fa.accept_16_7_3_15_1_2940 55 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 271
  (Polychromatic418967fa.accept_10_4_5_1_1_497 54 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 271 (accept_3_3 53 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 271 (accept_3_3 50 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 271 (accept_3_3 47 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 271 (Polychromatic418967fa.accept_10_6_5_1_1_482 46 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 115 271 (Polychromatic418967fa.accept_16_13_3_15_1_1931 45 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 271 (accept_3_3 44 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 115 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 271 (accept_3_3 41 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 115 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 115 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 271 (accept_3_3 38 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 115 271 (accept_3_3 35 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 115 271 (Polychromatic418967fa.accept_10_4_5_1_1_497 34 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 271 (accept_3_3 32 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 271 (accept_3_3 29 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 271 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 271 (accept_3_3 26 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 271 (Polychromatic418967fa.accept_19_6_1_5_1_5719 25 115
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 271 (accept_3_3 23 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 271 (accept_3_3 20 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 271
  (Polychromatic418967fa.accept_16_2_3_15_1_6309 18 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 271 (accept_3_3 17 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 271 (accept_3_3 14 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 271
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 271 (accept_3_3 11 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 271 (Polychromatic418967fa.accept_20_10_15_11_1_3759 10 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 271 (accept_3_3 8 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 271 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 115
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 271 (accept_3_3 5 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 115 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 271 (accept_3_3 2 115 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 115 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 271 (allA_succ_of_accept 113 114 271 (accept_3_3 113 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 114 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 112 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 114 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 111 114
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 271 (accept_3_3 110 114
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 114 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 114 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 108 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 271 (accept_3_3 107 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 114 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 106 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 114 271 (accept_3_3 104 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 114 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 103 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 114 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 102 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 271 (accept_3_3 101 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 271 (Polychromatic418967fa.accept_15_10_9_1_1_3688 100
  114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 271
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 99 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 114 271 (accept_3_3 98 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 114 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303 96 114
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 271 (accept_3_3 95 114
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 94 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 271 (accept_3_3 92 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 114 271 (Polychromatic418967fa.accept_11_3_4_7_1_114 91 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 114 271
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 90 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 114 271 (accept_3_3 89 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 114 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 87 114 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 271 (accept_3_3 86 114 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 85
  114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 114 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 114 271 (accept_3_3 83 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 114 271 (Polychromatic418967fa.accept_13_4_10_11_1_1908 82 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 271 (accept_3_3 80 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 114 271
  (Polychromatic418967fa.accept_21_15_9_19_1_10768 78 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 114 271 (accept_3_3 77 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 114 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 114 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 114 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 271 (accept_3_3 74 114 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 114 271
  (Polychromatic418967fa.accept_23_3_22_18_1_14998 72 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 114 271 (accept_3_3 71 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 114 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 114 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 271 (accept_3_3 68 114 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 271 (Polychromatic418967fa.accept_7_4_2_5_1_527
  67 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 66 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 114 271 (accept_3_3 65 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 114 271 (Polychromatic418967fa.accept_13_12_10_11_1_1279 64 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 114 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 271 (accept_3_3 62 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 114 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 114 271 (accept_3_3 59 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 114 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 271 (accept_3_3 56 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 271 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 271
  (Polychromatic418967fa.accept_13_2_10_11_1_1276 54 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 114 271 (accept_3_3 53 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 114 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 271 (Polychromatic418967fa.accept_13_12_10_11_1_1279 51
  114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 271 (accept_3_3 50
  114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 114 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 271 (accept_3_3 47 114 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 114 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 271 (accept_3_3 44
  114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 271
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 114 271 (Polychromatic418967fa.accept_13_3_10_11_1_1293 42 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 271 (accept_3_3 41 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 114 271 (accept_3_3 38 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 114 271 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 271 (accept_3_3 35 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 114 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 114 271 (accept_3_3 32 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 114 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 114 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 271 (accept_3_3 29 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 271 (Polychromatic418967fa.accept_13_2_10_11_1_1276 28 114 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 271
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 114 271 (accept_3_3 26 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 114 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 271 (accept_3_3 23 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 114 271 (accept_3_3 20 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 114 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 114 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 271 (accept_3_3 17 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 271
  (Polychromatic418967fa.accept_10_5_4_1_1_842 15 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 114 271 (accept_3_3 14 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 114 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 271 (accept_3_3 11 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 114 271 (accept_3_3 8 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  114 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 114 271 (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 271 (accept_3_3 5 114 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 114 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 114 271 (accept_3_3 2 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  114 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 114
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 271 (allA_of_3_1 113 113 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 271
  (allA_succ_of_accept 111 112 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 112 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 112 271 (accept_3_3 110 112 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 112 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 109 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 112 271
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 108 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 112 271 (accept_3_3 107 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 106 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 112 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 112 271 (accept_3_3 104 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 112 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 103 112 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 112 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 102 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 112 271 (accept_3_3 101 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 112 271 (Polychromatic418967fa.accept_13_9_8_11_1_725 100 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 112 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 112 271 (accept_3_3 98 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 97 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 112 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 96 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 112 271 (accept_3_3 95 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 112 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 94 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 112 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 112 271 (accept_3_3 92 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 112 271 (Polychromatic418967fa.accept_17_6_10_16_1_9453 91 112 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 112 271
  (Polychromatic418967fa.accept_19_14_17_5_1_15232 90 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 112 271 (accept_3_3 89 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 112 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 112 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 112 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 112 271 (accept_3_3 86 112 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 112 271
  (Polychromatic418967fa.accept_15_10_7_1_1_3686 85 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 112 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 112 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 112 271 (accept_3_3 83 112 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 112 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 112 271 (accept_3_3 80 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 112 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 78 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 112 271 (accept_3_3 77 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 112 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 76 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 112 271 (accept_3_3 74 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 112 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 73 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 112 271 (Polychromatic418967fa.accept_19_15_17_5_1_3052 72 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 112 271 (accept_3_3 71 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 112 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 112 271 (accept_3_3 68 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 112 271 (Polychromatic418967fa.accept_21_4_7_19_1_13687 67 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 112 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 271 (accept_3_3 65 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 112 271 (Polychromatic418967fa.accept_11_9_2_7_1_1298 64 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 112 271 (accept_3_3 62 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 112 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 271 (accept_3_3 59 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 112 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 271 (accept_3_3 56 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 271 (Polychromatic418967fa.accept_13_3_8_11_1_1906 55 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 271 (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 271 (accept_3_3 53 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 112 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 271 (accept_3_3 50 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 271 (accept_3_3 47 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 271 (accept_3_3 44 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 271 (accept_3_3 41 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 271 (Polychromatic418967fa.accept_13_1_8_11_1_724 40 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 271 (accept_3_3 38 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 271 (Polychromatic418967fa.accept_19_18_17_5_1_4343 37 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 271 (accept_3_3 35 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 112 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 271 (accept_3_3 32 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 271 (Polychromatic418967fa.accept_11_9_2_7_1_1298 31 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 271 (accept_3_3 29 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 271 (Polychromatic418967fa.accept_31_28_19_23_1_16603 28 112 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 271 (accept_3_3 26 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 271 (accept_3_3 23 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 271 (accept_3_3 20 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 271 (Polychromatic418967fa.accept_19_18_17_5_1_4343 18 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 271 (accept_3_3 17 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 112 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 271 (accept_3_3 14 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 112 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 271 (accept_3_3 11 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 271 (accept_3_3 8 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 271 (accept_3_3 5 112 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 271 (Polychromatic418967fa.accept_13_4_8_11_1_1937 4 112 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 271 (accept_3_3 2 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 271 (Polychromatic418967fa.accept_13_1_8_11_1_724 1 112 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 271 (allA_succ_of_accept 110 111 271 (accept_3_3 110 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 109 111 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 271 (Polychromatic418967fa.accept_13_4_7_11_1_1981 108
  111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 271 (accept_3_3 107
  111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 271
  (Polychromatic418967fa.accept_6_4_3_1_1_57 106 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 111 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 105 111 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 271 (accept_3_3 104 111 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 111 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 103 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 102 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 111 271 (accept_3_3 101 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 111 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 99 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 271 (accept_3_3 98 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 97 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 96 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 111 271 (accept_3_3 95 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 111 271 (Polychromatic418967fa.accept_12_9_3_7_1_924 93 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 271 (accept_3_3 92 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 271 (Polychromatic418967fa.accept_17_6_9_16_1_4410 91 111
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 271
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 90 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 111 271 (accept_3_3 89 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 111 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 111 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 111 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 271 (accept_3_3 86 111 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 85
  111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 271
  (Polychromatic418967fa.accept_15_9_6_1_1_493 84 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 271 (accept_3_3 83 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 111 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 271 (accept_3_3 80 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 78 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 271 (accept_3_3 77 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 271 (Polychromatic418967fa.accept_21_12_6_19_1_1871 75 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 271 (accept_3_3 74 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 271 (Polychromatic418967fa.accept_23_4_19_18_1_15015 73
  111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 271
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 72 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 111 271 (accept_3_3 71 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 271 (accept_3_3 68 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 271
  (Polychromatic418967fa.accept_13_1_7_11_1_702 66 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 271 (accept_3_3 65 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 271 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 271 (accept_3_3 62 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 111 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 271 (accept_3_3 59 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 271 (accept_3_3 56 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 271 (Polychromatic418967fa.accept_13_3_7_11_1_1904 55 111 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 271
  (Polychromatic418967fa.accept_15_9_6_1_1_493 54 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 271 (accept_3_3 53 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 271 (accept_3_3 50 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 271
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 48 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 271 (accept_3_3 47 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 271 (Polychromatic418967fa.accept_12_9_3_7_1_924 45 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 271 (accept_3_3 44 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 111 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 271 (accept_3_3 41 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 271 (accept_3_3 38 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 271 (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 271 (accept_3_3 35 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 271 (accept_3_3 32 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 271
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 30 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 271 (accept_3_3 29 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 271 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 271 (accept_3_3 26 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 111 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 271 (accept_3_3 23 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 271 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 271 (accept_3_3 20 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 271 (Polychromatic418967fa.accept_24_19_15_7_1_9853 19 111
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 271 (accept_3_3 17 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 271 (accept_3_3 14 111 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 271
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 271 (accept_3_3 11 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 111 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 271 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 111 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 271 (accept_3_3 8 111 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 271 (accept_3_3 5 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 271 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 271 (accept_3_3 2 111 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 111 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 271 (allA_of_3_1 110 110 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 271
  (allA_succ_of_accept 108 109 271 (Polychromatic418967fa.accept_10_8_9_1_1_189 108 109 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 271 (accept_3_3 107 109 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 271
  (Polychromatic418967fa.accept_10_5_9_1_1_187 105 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 271 (accept_3_3 104 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 271 (Polychromatic418967fa.accept_19_8_14_5_1_9919 103 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 271 (accept_3_3 101 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 100 109
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 99 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 271 (accept_3_3 98 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 97 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 271 (Polychromatic418967fa.accept_21_12_4_19_1_4526 96 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 271 (accept_3_3 95 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 109 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 93 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 271 (accept_3_3 92 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 271 (Polychromatic418967fa.accept_11_3_10_7_1_129 91 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 271 (accept_3_3 89 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 271 (Polychromatic418967fa.accept_10_8_9_1_1_189 88 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 271
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 87 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 271 (accept_3_3 86 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 271 (Polychromatic418967fa.accept_13_6_5_11_1_1971 84 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 271 (accept_3_3 83 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 109 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 271
  (Polychromatic418967fa.accept_13_3_5_11_1_716 81 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 271 (accept_3_3 80 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 271 (accept_3_3 77 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 271
  (Polychromatic418967fa.accept_10_5_9_1_1_187 75 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 271 (accept_3_3 74 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 271 (Polychromatic418967fa.accept_19_16_14_5_1_9920 73 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 271 (accept_3_3 71 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 271 (accept_3_3 68 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 271 (Polychromatic418967fa.accept_16_3_13_15_1_1913 67 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 271 (accept_3_3 65 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 271
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 271 (accept_3_3 62 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 271 (Polychromatic418967fa.accept_17_10_7_16_1_6841 61 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 271 (Polychromatic418967fa.accept_16_12_13_15_1_1966 60 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 271 (accept_3_3 59 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 109 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 271 (accept_3_3 56 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 271 (accept_3_3 53 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 271 (Polychromatic418967fa.accept_10_2_9_1_1_185 52 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 271 (accept_3_3 50 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 271 (Polychromatic418967fa.accept_19_11_14_5_1_5629 49 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 271 (accept_3_3 47 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 271
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 271 (accept_3_3 44 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 271 (accept_3_3 41 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 271 (Polychromatic418967fa.accept_17_6_7_16_1_6836 40 109 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 271
  (Polychromatic418967fa.accept_21_18_4_19_1_1838 39 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 109 271 (accept_3_3 38 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 109 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 109 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 109 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 271 (accept_3_3 35 109 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 271
  (Polychromatic418967fa.accept_13_7_5_11_1_1927 33 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 271 (accept_3_3 32 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 271 (Polychromatic418967fa.accept_21_10_4_19_1_3136 31 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 271 (accept_3_3 29 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 271 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 271 (accept_3_3 26 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 271 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 271 (Polychromatic418967fa.accept_23_1_17_18_1_11769 24 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 271 (accept_3_3 23 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 271
  (Polychromatic418967fa.accept_19_2_14_5_1_5715 21 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 271 (accept_3_3 20 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 271 (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 271 (accept_3_3 17 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 271 (accept_3_3 14 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 271 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 271 (accept_3_3 11 109 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 271 (accept_3_3 8 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 271 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 271 (accept_3_3 5 109 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 271 (Polychromatic418967fa.accept_29_4_22_10_1_16602 4 109 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 271
  (Polychromatic418967fa.accept_11_3_10_7_1_129 3 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 271 (accept_3_3 2 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 109 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 271 (allA_succ_of_accept 107 108 271 (accept_3_3 107 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 108 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 106 108 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 271 (Polychromatic418967fa.accept_19_10_13_5_1_3091 105
  108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 271 (accept_3_3 104
  108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 108 271
  (Polychromatic418967fa.accept_10_3_8_1_1_182 103 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 108 271 (Polychromatic418967fa.accept_19_7_13_5_1_7125 102 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 271 (accept_3_3 101 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 100 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 99 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 108 271 (accept_3_3 98 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 108 271 (Polychromatic418967fa.accept_13_6_4_11_1_282 97 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 108 271 (Polychromatic418967fa.accept_14_12_10_5_1_2712 96 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 108 271 (accept_3_3 95 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 271 (Polychromatic418967fa.accept_15_4_3_1_1_487 94 108
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 93 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 108 271 (accept_3_3 92 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 108 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 91 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 108 271 (Polychromatic418967fa.accept_11_2_9_7_1_124 90 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 108 271 (accept_3_3 89 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 271 (Polychromatic418967fa.accept_13_10_4_11_1_1969 88 108
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 271
  (Polychromatic418967fa.accept_19_11_13_5_1_5714 87 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 108 271 (accept_3_3 86 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 108 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 108 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 108 271 (Polychromatic418967fa.accept_13_6_4_11_1_282 84 108
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 271 (accept_3_3 83 108
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 271
  (Polychromatic418967fa.accept_11_5_9_7_1_411 82 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 108 271 (Polychromatic418967fa.accept_15_6_3_1_1_3678 81 108 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 108 271 (accept_3_3 80 108 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 108 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 79 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 108 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 78
  108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 271 (accept_3_3 77
  108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 271
  (Polychromatic418967fa.accept_24_4_12_7_1_16601 76 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 108 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 271 (accept_3_3 74 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 271 (Polychromatic418967fa.accept_10_3_8_1_1_182 73 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 108 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 72 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 108 271 (accept_3_3 71 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 108 271 (Polychromatic418967fa.accept_25_20_8_21_1_13155 70 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 271 (accept_3_3 68 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 108 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 108 271
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 66 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 108 271 (accept_3_3 65 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 108 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 108 271 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 271 (accept_3_3 62 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 271 (Polychromatic418967fa.accept_16_13_12_15_1_6290 61
  108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 108 271
  (Polychromatic418967fa.accept_11_5_9_7_1_411 60 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 108 271 (accept_3_3 59 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 108 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 108 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 271 (accept_3_3 56 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 271 (Polychromatic418967fa.accept_41_14_26_25_1_16600 55 108 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 271
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 54 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 108 271 (accept_3_3 53 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 108 271 (Polychromatic418967fa.accept_16_4_12_15_1_6289 52 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 108 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 271 (accept_3_3 50 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 271
  (Polychromatic418967fa.accept_19_10_13_5_1_3091 48 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 108 271 (accept_3_3 47 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 108 271 (Polychromatic418967fa.accept_11_2_9_7_1_124 46 108 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 271 (Polychromatic418967fa.accept_13_6_4_11_1_282 45 108
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 271 (accept_3_3 44 108
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 108 271 (Polychromatic418967fa.accept_24_18_12_7_1_14861 42 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 271 (accept_3_3 41 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 271 (Polychromatic418967fa.accept_14_12_10_5_1_2712 40 108 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 271
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 108 271 (accept_3_3 38 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 108 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 108 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 271 (accept_3_3 35 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 271 (Polychromatic418967fa.accept_13_8_4_11_1_3469 34 108 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 271
  (Polychromatic418967fa.accept_10_3_8_1_1_182 33 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 271 (accept_3_3 32 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 108 271 (Polychromatic418967fa.accept_19_12_13_5_1_11331 31 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 271 (accept_3_3 29 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 271 (Polychromatic418967fa.accept_13_2_4_11_1_2003 28 108
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 271
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 108 271 (accept_3_3 26 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 108 271 (Polychromatic418967fa.accept_13_12_4_11_1_1925 25 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 108 271 (Polychromatic418967fa.accept_11_2_9_7_1_124 24 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 271 (accept_3_3 23 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 108 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 271
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 271 (accept_3_3 20 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 108 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 108 271 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 271 (accept_3_3 17 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 108 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 108 271 (accept_3_3 14 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 108 271 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 108 271 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 271 (accept_3_3 11 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 271 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 108
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 108 271 (accept_3_3 8 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  108 271 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 108 271 (Polychromatic418967fa.accept_13_6_4_11_1_282 6 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 271 (accept_3_3 5 108 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 271 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 108 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 271
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 108 271 (accept_3_3 2 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  108 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 108 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 108
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 271 (allA_of_3_1 107 107 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 271
  (allA_succ_of_accept 105 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 106 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 271 (accept_3_3 104 106 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 106 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 103 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 102 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 106 271 (accept_3_3 101 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 106 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 100 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 106 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 271 (accept_3_3 98 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 96 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 271 (accept_3_3 95 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 94 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 271 (accept_3_3 92 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 271 (Polychromatic418967fa.accept_16_11_10_15_1_6301 91 106 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 90 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 106 271 (accept_3_3 89 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 106 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 88 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 106 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 271 (accept_3_3 86 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 84 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 271 (accept_3_3 83 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 271 (Polychromatic418967fa.accept_10_2_6_1_1_1296 82 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 271 (accept_3_3 80 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 271 (Polychromatic418967fa.accept_18_7_16_1_1_4951 79 106 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 271 (accept_3_3 77 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 271 (accept_3_3 74 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 271
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 271 (accept_3_3 71 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 271 (Polychromatic418967fa.accept_19_13_11_5_1_5692 70 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 271 (accept_3_3 68 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 271 (accept_3_3 65 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 271 (accept_3_3 62 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 271 (accept_3_3 59 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 271 (accept_3_3 56 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 271
  (Polychromatic418967fa.accept_17_3_4_16_1_3208 54 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 271 (accept_3_3 53 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 271 (accept_3_3 50 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 271 (accept_3_3 47 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 271 (accept_3_3 44 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 271 (Polychromatic418967fa.accept_13_4_2_11_1_733 43 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 271 (accept_3_3 41 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 271 (accept_3_3 38 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 271
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 106 271 (accept_3_3 35 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 106 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 106 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 271 (accept_3_3 32 106 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31
  106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 271 (accept_3_3 29 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 271 (accept_3_3 26 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 271 (accept_3_3 23 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 271 (accept_3_3 20 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 271 (Polychromatic418967fa.accept_22_19_18_7_1_16579 19 106 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 271 (accept_3_3 17 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 271 (accept_3_3 14 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 271 (accept_3_3 11 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 271 (accept_3_3 8 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 271 (accept_3_3 5 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 106 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 271 (accept_3_3 2 106 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 271 (allA_succ_of_accept 104 105 271 (accept_3_3 104 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 103 105 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 105
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 271 (accept_3_3 101 105
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 271
  (Polychromatic418967fa.accept_6_4_3_1_1_57 100 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 99 105 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 271 (accept_3_3 98 105 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 105 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 97 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 271 (Polychromatic418967fa.accept_10_6_5_1_1_482
  96 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 271 (accept_3_3 95
  105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 94 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 105 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 271 (accept_3_3 92 105 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 105 271 (Polychromatic418967fa.accept_19_15_10_5_1_5637 91 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 105 271 (accept_3_3 89 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 105 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 105 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 87 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 271 (accept_3_3 86 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 85 105 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 105 271 (accept_3_3 83 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 105 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 105 271 (Polychromatic418967fa.accept_13_3_1_11_1_1268 81 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 271 (accept_3_3 80 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 105 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 105 271 (accept_3_3 77 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 105 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 105 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 271 (accept_3_3 74 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 271 (Polychromatic418967fa.accept_13_8_1_11_1_1284 73 105 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 271
  (Polychromatic418967fa.accept_13_7_1_11_1_732 72 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 105 271 (accept_3_3 71 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 105 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 105 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 271 (accept_3_3 68 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 105 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 271 (accept_3_3 65 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 105 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 105 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 271 (accept_3_3 62 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 105 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 271
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 60 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 105 271 (accept_3_3 59 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 105 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 271 (accept_3_3 56 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 271 (Polychromatic418967fa.accept_13_3_1_11_1_1268 55 105 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 271 (accept_3_3 53 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 51 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 271 (accept_3_3 50 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 105 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 271 (accept_3_3 47 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 271 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 271 (accept_3_3 44 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 105 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 271 (accept_3_3 41 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 271 (accept_3_3 38 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 271 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 271
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 271 (accept_3_3 35 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 271 (Polychromatic418967fa.accept_13_7_1_11_1_732 33 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 271 (accept_3_3 32 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 105 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 271 (accept_3_3 29 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 271 (accept_3_3 26 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 105 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 271
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 271 (accept_3_3 23 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 271 (accept_3_3 20 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 271 (accept_3_3 17 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 15 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 271 (accept_3_3 14 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 105 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 271 (accept_3_3 11 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 271 (accept_3_3 8 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 271 (accept_3_3 5 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 271 (accept_3_3 2 105 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 271 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 105 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 271 (allA_of_3_1 104 104 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 271
  (allA_succ_of_accept 102 103 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 102 103 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 271 (accept_3_3 101 103 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 271 (Polychromatic418967fa.accept_15_10_13_1_1_3698 100 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 271
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 99 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 271 (accept_3_3 98 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 97 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 96 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 271 (accept_3_3 95 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 271 (Polychromatic418967fa.accept_16_14_7_15_1_3947 94 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 93 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 271 (accept_3_3 92 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 271 (Polychromatic418967fa.accept_11_3_4_7_1_114 91 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 271 (Polychromatic418967fa.accept_17_5_1_16_1_4359 90 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 271 (accept_3_3 89 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 87 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 271 (accept_3_3 86 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303 85 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 271 (accept_3_3 83 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 271 (Polychromatic418967fa.accept_10_2_3_1_1_481 82 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 271
  (Polychromatic418967fa.accept_25_6_3_21_1_16599 81 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 103 271 (accept_3_3 80 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 103 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 103 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 103 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 78 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 271 (accept_3_3 77 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 271
  (Polychromatic418967fa.accept_22_10_15_7_1_16598 76 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 103 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 103 271 (accept_3_3 74 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 103 271 (Polychromatic418967fa.accept_17_5_1_16_1_4359 73 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 271
  (Polychromatic418967fa.accept_10_2_3_1_1_481 72 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 103 271 (accept_3_3 71 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 103 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 103 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 271 (accept_3_3 68 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 103 271 (Polychromatic418967fa.accept_16_3_7_15_1_1130 67 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 103 271 (accept_3_3 65 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 103 271 (Polychromatic418967fa.accept_18_10_13_1_1_7736 64 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 103 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 271 (accept_3_3 62 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 103 271 (accept_3_3 59 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 271 (Polychromatic418967fa.accept_10_8_3_1_1_1316 58 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 271 (accept_3_3 56 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 271 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 271
  (Polychromatic418967fa.accept_16_6_7_15_1_1942 54 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 271 (accept_3_3 53 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 271 (accept_3_3 50 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 271 (Polychromatic418967fa.accept_13_10_12_11_1_731 49 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 271 (accept_3_3 47 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 271 (Polychromatic418967fa.accept_13_7_12_11_1_1911 46 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 271 (Polychromatic418967fa.accept_25_20_3_21_1_16597 45 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 271 (accept_3_3 44 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 271 (accept_3_3 41 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 271 (Polychromatic418967fa.accept_13_1_12_11_1_728 40 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 271 (accept_3_3 38 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 271 (Polychromatic418967fa.accept_27_10_22_1_1_16596 37 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 271
  (Polychromatic418967fa.accept_11_3_4_7_1_114 36 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 271 (accept_3_3 35 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 271 (accept_3_3 32 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 271 (Polychromatic418967fa.accept_19_12_8_5_1_8538 31 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 271 (accept_3_3 29 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 271 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 271 (Polychromatic418967fa.accept_13_1_12_11_1_728 27 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 271 (accept_3_3 26 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 271 (accept_3_3 23 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 271 (Polychromatic418967fa.accept_10_2_3_1_1_481 22 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 271 (accept_3_3 20 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 271
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 271 (accept_3_3 17 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 271 (accept_3_3 14 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 271 (Polychromatic418967fa.accept_19_13_8_5_1_8539 13 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 271 (accept_3_3 11 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 271 (Polychromatic418967fa.accept_13_10_12_11_1_731 10 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 271 (Polychromatic418967fa.accept_22_9_15_7_1_2581 9 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 271 (accept_3_3 8 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 271 (accept_3_3 5 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 271 (Polychromatic418967fa.accept_13_4_12_11_1_5362 4 103 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 271 (accept_3_3 2 103 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 271 (Polychromatic418967fa.accept_13_1_12_11_1_728 1 103 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 271 (allA_succ_of_accept 101 102 271 (accept_3_3 101 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 102 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 100 102 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 102 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 99 102 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 271 (accept_3_3 98 102 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 97
  102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 96 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 271 (accept_3_3 95 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 102 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 94 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 271 (accept_3_3 92 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 271 (Polychromatic418967fa.accept_21_7_18_19_1_10715 91 102 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 90 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 102 271 (accept_3_3 89 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 102 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 102 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 271 (accept_3_3 86 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 271
  (Polychromatic418967fa.accept_22_18_14_7_1_16595 84 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 102 271 (accept_3_3 83 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 102 271 (Polychromatic418967fa.accept_19_6_7_5_1_256 82 102 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 102 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 271 (accept_3_3 80 102 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 271 (Polychromatic418967fa.accept_7_2_4_5_1_313
  79 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 78 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 102 271 (accept_3_3 77 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 102 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 102 271 (Polychromatic418967fa.accept_18_3_12_1_1_3787 75 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 271 (accept_3_3 74 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 102 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 72 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 102 271 (accept_3_3 71 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 102 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 271 (accept_3_3 68 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 271
  (Polychromatic418967fa.accept_10_6_2_1_1_494 66 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 102 271 (accept_3_3 65 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 102 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 102 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 271 (accept_3_3 62 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 102 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 271 (accept_3_3 59 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 102 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 271 (accept_3_3 56 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 271
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 102 271 (accept_3_3 53 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 102 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 102 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 271 (accept_3_3 50 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 102 271 (accept_3_3 47 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 102 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 271 (accept_3_3 44 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 271 (accept_3_3 41 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 271 (accept_3_3 38 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 102 271 (accept_3_3 35 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 102 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 271 (accept_3_3 32 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 102 271 (accept_3_3 29 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 102 271 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 102 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 271 (accept_3_3 26 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 271 (accept_3_3 23 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 271 (accept_3_3 20 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 271
  (Polychromatic418967fa.accept_22_18_14_7_1_16595 18 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 271 (accept_3_3 17 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 102 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 102 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 271 (accept_3_3 14 102 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 271
  (Polychromatic418967fa.accept_19_12_7_5_1_5725 12 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 271 (accept_3_3 11 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 271 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 271 (accept_3_3 8 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 271 (accept_3_3 5 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 102 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 271 (accept_3_3 2 102 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 271 (allA_of_3_1 101 101 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 271 (allA_succ_of_accept 99
  100 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 100 271 (accept_3_3 98 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 100 271 (Polychromatic418967fa.accept_15_7_10_1_1_1836 97 100 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 271 (Polychromatic418967fa.accept_15_6_10_1_1_3675 96 100
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 100 271 (accept_3_3 95 100
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 100 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 94 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 100 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 100 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 100 271 (accept_3_3 92 100 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 100 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 91 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 100 271
  (Polychromatic418967fa.accept_27_9_19_1_1_16594 90 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 100 271 (accept_3_3 89 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 100 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 100 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 100 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 100 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 100 271 (accept_3_3 86 100 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 100 271 (Polychromatic418967fa.accept_13_7_9_11_1_705
  85 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 100 271
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 84 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 100 271 (accept_3_3 83 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 100 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 100 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 100 271 (accept_3_3 80 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 100 271 (Polychromatic418967fa.accept_13_1_9_11_1_703 79 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 100 271
  (Polychromatic418967fa.accept_16_14_4_15_1_3944 78 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 100 271 (accept_3_3 77 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 100 271 (Polychromatic418967fa.accept_16_12_4_15_1_5091 76 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 100 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 75
  100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 100 271 (accept_3_3 74
  100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 100 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 73 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 100 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 72 100 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 100 271 (accept_3_3 71 100 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 100 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 100 271 (accept_3_3 68 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 100 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 100 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 100 271 (accept_3_3 65 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 100 271 (Polychromatic418967fa.accept_21_1_16_19_1_3134 64 100 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 100 271 (accept_3_3 62 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 100 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 61 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 100 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 100 271 (accept_3_3 59 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 100 271 (accept_3_3 56 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 100 271 (Polychromatic418967fa.accept_17_4_15_16_1_3231 55 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 100 271 (Polychromatic418967fa.accept_13_2_9_11_1_258 54 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 100 271 (accept_3_3 53 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 100 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 100 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 100 271 (accept_3_3 50 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 100 271 (Polychromatic418967fa.accept_14_7_2_5_1_4528 49 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 100 271 (Polychromatic418967fa.accept_17_14_15_16_1_1271 48 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 271 (accept_3_3 47 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 100 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 100 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 100 271 (accept_3_3 44 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 100 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 100 271 (Polychromatic418967fa.accept_26_16_22_11_1_16593 42 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 100 271 (accept_3_3 41 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 100 271 (Polychromatic418967fa.accept_13_1_9_11_1_703 40 100
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 100 271 (accept_3_3 38 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 100 271 (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 100 271 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 271 (accept_3_3 35 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 100 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 100
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 100 271 (accept_3_3 32 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 100 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 100 271 (Polychromatic418967fa.accept_16_14_4_15_1_3944 30 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 271 (accept_3_3 29 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 100
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 271 (accept_3_3 26 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 100 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 100 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 271 (accept_3_3 23 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 271 (accept_3_3 20 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 271 (accept_3_3 17 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 271 (Polychromatic418967fa.accept_18_16_10_1_1_3696 16 100 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 271 (accept_3_3 14 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 271 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 271 (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 271 (accept_3_3 11 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 100 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 271 (accept_3_3 8 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 271 (Polychromatic418967fa.accept_13_7_9_11_1_705 7 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 271 (accept_3_3 5 100 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 100 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 271 (accept_3_3 2 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 271 (Polychromatic418967fa.accept_13_1_9_11_1_703 1 100 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  271 (allA_succ_of_accept 98 99 271 (accept_3_3 98 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 97 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 271 (Polychromatic418967fa.accept_15_6_9_1_1_1823 96 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 271 (accept_3_3 95 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 93 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 271 (accept_3_3 92 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 271 (Polychromatic418967fa.accept_16_11_3_15_1_1989 91 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 271 (accept_3_3 89 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 87 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 271 (accept_3_3 86 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 271 (Polychromatic418967fa.accept_10_5_9_1_1_187 85 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 271 (accept_3_3 83 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 81 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 271 (accept_3_3 80 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 271 (Polychromatic418967fa.accept_13_1_8_11_1_724 79 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 271 (Polychromatic418967fa.accept_10_8_9_1_1_189 78 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 271 (accept_3_3 77 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 271
  (Polychromatic418967fa.accept_10_5_9_1_1_187 75 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 271 (accept_3_3 74 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 271 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 271 (accept_3_3 71 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 271 (accept_3_3 68 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 271 (accept_3_3 65 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 271
  (Polychromatic418967fa.accept_19_6_4_5_1_5650 63 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 271 (accept_3_3 62 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 271 (Polychromatic418967fa.accept_13_9_8_11_1_725 61 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 271 (accept_3_3 59 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 271 (accept_3_3 56 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 271 (Polychromatic418967fa.accept_21_12_15_19_1_10743 54 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 271 (accept_3_3 53 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 271
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 271 (accept_3_3 50 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 271 (Polychromatic418967fa.accept_13_10_8_11_1_1985 49 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 271 (accept_3_3 47 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 271 (accept_3_3 44 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 271 (Polychromatic418967fa.accept_13_4_8_11_1_1937 43 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 271 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 271 (accept_3_3 41 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 271 (accept_3_3 38 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 271 (Polychromatic418967fa.accept_15_7_9_1_1_473 37 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 271 (accept_3_3 35 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 271 (accept_3_3 32 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 271 (Polychromatic418967fa.accept_13_4_8_11_1_1937 30 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 271 (accept_3_3 29 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 271 (accept_3_3 26 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 271 (accept_3_3 23 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 271 (accept_3_3 20 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 271 (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 271 (accept_3_3 17 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 271
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 271 (accept_3_3 14 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 271 (accept_3_3 11 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 99 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 271 (accept_3_3 8 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  271 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 99 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 271 (accept_3_3 5 99 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 271 (accept_3_3 2 99 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 271 (Polychromatic418967fa.accept_13_1_8_11_1_724 1
  99 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  271 (allA_of_3_1 98 98 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 271 (allA_succ_of_accept 96 97 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 96 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 271 (accept_3_3 95 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 93 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 271 (accept_3_3 92 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 271 (Polychromatic418967fa.accept_16_11_1_15_1_1123 91 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 271 (accept_3_3 89 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 87 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 271 (accept_3_3 86 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 85 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 84 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 271 (accept_3_3 83 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 271 (accept_3_3 80 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 271 (Polychromatic418967fa.accept_11_2_9_7_1_124 79 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 271 (accept_3_3 77 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 271 (accept_3_3 74 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 271 (Polychromatic418967fa.accept_13_8_6_11_1_1979 73 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 271
  (Polychromatic418967fa.accept_16_8_1_15_1_1982 72 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 271 (accept_3_3 71 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 271 (accept_3_3 68 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 271 (accept_3_3 65 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 271 (Polychromatic418967fa.accept_23_17_5_18_1_10069 63 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 271 (accept_3_3 62 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 271 (Polychromatic418967fa.accept_19_4_2_5_1_5677 61 97 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 271 (accept_3_3 59 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 271 (accept_3_3 56 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 271 (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 271 (accept_3_3 53 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 271 (Polychromatic418967fa.accept_17_1_12_16_1_2211 52 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 271 (accept_3_3 50 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 271 (accept_3_3 47 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 271 (Polychromatic418967fa.accept_17_11_12_16_1_3219 45 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 271 (accept_3_3 44 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 97 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 271 (accept_3_3 41 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 271 (accept_3_3 38 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 271 (Polychromatic418967fa.accept_16_5_1_15_1_3922 37 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 271 (accept_3_3 35 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 271 (accept_3_3 32 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 271 (accept_3_3 29 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 271 (Polychromatic418967fa.accept_17_11_12_16_1_3219 28 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 271 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 271 (accept_3_3 26 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 271 (accept_3_3 23 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 271 (accept_3_3 20 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 271 (Polychromatic418967fa.accept_24_19_1_7_1_9846 19 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 271 (accept_3_3 17 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 271 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 271 (accept_3_3 14 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 271 (accept_3_3 11 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 271 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 271 (accept_3_3 8 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 271 (Polychromatic418967fa.accept_19_7_2_5_1_5680 7 97 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 271 (accept_3_3 5 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 97 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 97 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 271 (accept_3_3 2 97 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 97 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 271
  (allA_succ_of_accept 95 96 271 (accept_3_3 95 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  96 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 94 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 96 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 96 271 (accept_3_3 92 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 271 (Polychromatic418967fa.accept_14_7_12_5_1_1861 91 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 271
  (Polychromatic418967fa.accept_17_5_11_16_1_3257 90 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 96 271 (accept_3_3 89 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  96 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 88 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 96 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 87 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 271 (accept_3_3 86 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 85 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 271 (accept_3_3 83 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  96 271 (Polychromatic418967fa.accept_10_2_6_1_1_1296 82 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 271 (Polychromatic418967fa.accept_11_4_8_7_1_819 81 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 271 (accept_3_3 80 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 271
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 78 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 96 271 (accept_3_3 77 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  96 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 96 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 271 (accept_3_3 74 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 271 (Polychromatic418967fa.accept_14_3_12_5_1_153 73 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 271
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 271 (accept_3_3 71 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  96 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 271 (Polychromatic418967fa.accept_15_9_6_1_1_493 69 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 271 (accept_3_3 68 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 271 (accept_3_3 65 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 271 (Polychromatic418967fa.accept_21_1_12_19_1_7721 64 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 271 (Polychromatic418967fa.accept_14_7_12_5_1_1861 63 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 271 (accept_3_3 62 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 96 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 271
  (Polychromatic418967fa.accept_19_3_1_5_1_8549 60 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 271 (accept_3_3 59 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 271 (accept_3_3 56 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 271 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 271
  (Polychromatic418967fa.accept_15_9_6_1_1_493 54 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 271 (accept_3_3 53 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 271 (Polychromatic418967fa.accept_21_9_12_19_1_12172 51 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 271 (accept_3_3 50 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 96 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 271 (accept_3_3 47 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 271 (Polychromatic418967fa.accept_13_7_5_11_1_1927 46 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 271 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 271 (accept_3_3 44 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 271
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 271 (accept_3_3 41 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 271 (accept_3_3 38 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 271
  (Polychromatic418967fa.accept_21_15_12_19_1_10724 36 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 96 271 (accept_3_3 35 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 96 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 96 271 (Polychromatic418967fa.accept_13_7_5_11_1_1927 33 96
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 271 (accept_3_3 32 96 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 31
  96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 271 (accept_3_3 29 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 271 (Polychromatic418967fa.accept_19_9_1_5_1_11278 28 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 271 (accept_3_3 26 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 271
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 271 (accept_3_3 23 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 271 (accept_3_3 20 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 271 (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 271
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 271 (accept_3_3 17 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 271 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 271 (accept_3_3 14 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 271 (accept_3_3 11 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 271 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 271 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 271 (accept_3_3 8 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 271
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 271 (accept_3_3 5 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  271 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 96 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 96 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 271 (accept_3_3 2 96 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 271 (Polychromatic418967fa.accept_20_1_16_11_1_9579 1 96 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 271
  (allA_of_3_1 95 95 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 271 (allA_succ_of_accept 93 94 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 94 271 (accept_3_3 92 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  94 271 (Polychromatic418967fa.accept_17_6_9_16_1_4410 91 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 94 271 (Polychromatic418967fa.accept_16_10_14_15_1_2933 90 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 271 (accept_3_3 89 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 94 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 94 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 94 271 (accept_3_3 86 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  94 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 94 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 271 (accept_3_3 83 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 271 (Polychromatic418967fa.accept_14_12_10_5_1_2712 82 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 271 (accept_3_3 80 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 79 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 271 (accept_3_3 77 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 271 (accept_3_3 74 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 271 (accept_3_3 71 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 271 (accept_3_3 68 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 67 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 271 (accept_3_3 65 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 271 (accept_3_3 62 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 271 (accept_3_3 59 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 271 (accept_3_3 56 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 271 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 271 (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 271 (accept_3_3 53 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 94 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 271 (accept_3_3 50 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 271 (accept_3_3 47 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 271 (Polychromatic418967fa.accept_13_7_3_11_1_280 46 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 271 (accept_3_3 44 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 271 (accept_3_3 41 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 271 (accept_3_3 38 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 271 (accept_3_3 35 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 271 (accept_3_3 32 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 271 (Polychromatic418967fa.accept_13_5_3_11_1_1288 31 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 271 (accept_3_3 29 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 271 (accept_3_3 26 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 271 (accept_3_3 23 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 271 (accept_3_3 20 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 271 (Polychromatic418967fa.accept_24_19_22_7_1_8111 19 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 271 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 271 (accept_3_3 17 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 94 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 271 (accept_3_3 14 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 271 (accept_3_3 11 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 271 (Polychromatic418967fa.accept_13_10_3_11_1_1923 10 94 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 271 (accept_3_3 8 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 94 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 94 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 271 (accept_3_3 5 94 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 94 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 271 (accept_3_3 2 94 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 271
  (allA_succ_of_accept 92 93 271 (accept_3_3 92 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 271 (Polychromatic418967fa.accept_14_7_9_5_1_529 91 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 271 (accept_3_3 89 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 87 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 271 (accept_3_3 86 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 85 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 271 (Polychromatic418967fa.accept_18_12_3_1_1_3685 84 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 271 (accept_3_3 83 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 93 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 81 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 271 (accept_3_3 80 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 271 (accept_3_3 77 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 271
  (Polychromatic418967fa.accept_11_9_5_7_1_815 75 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 271 (accept_3_3 74 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 271 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 271 (accept_3_3 71 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 69 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 271 (accept_3_3 68 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 271 (accept_3_3 65 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 271 (accept_3_3 62 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 271 (accept_3_3 59 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 271
  (Polychromatic418967fa.accept_21_15_9_19_1_10768 57 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 93 271 (accept_3_3 56 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 271 (Polychromatic418967fa.accept_13_3_2_11_1_1999 55 93 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 271 (accept_3_3 53 93 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52
  93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 271 (accept_3_3 50 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 271 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 271 (accept_3_3 47 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 271 (accept_3_3 44 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 271 (accept_3_3 41 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 271 (accept_3_3 38 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 271 (Polychromatic418967fa.accept_19_18_17_5_1_4343 37 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 271 (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 271 (accept_3_3 35 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 271 (accept_3_3 32 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 271 (accept_3_3 29 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 271 (accept_3_3 26 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 271 (accept_3_3 23 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 271
  (Polychromatic418967fa.accept_14_7_9_5_1_529 21 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 271 (accept_3_3 20 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 271 (Polychromatic418967fa.accept_15_4_3_1_1_487 19 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 271 (accept_3_3 17 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 271 (accept_3_3 14 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 271 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 271 (accept_3_3 11 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 271
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 271 (accept_3_3 8 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 271 (accept_3_3 5 93 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 271 (accept_3_3 2 93 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 271
  (Polychromatic418967fa.accept_25_1_18_21_1_16592 1 93 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 92 271 (allA_of_3_1 92 92 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 271
  (allA_succ_of_accept 90 91 271 (Polychromatic418967fa.accept_16_10_11_15_1_6302 90 91 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 271 (accept_3_3 89 91 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 271 (Polychromatic418967fa.accept_19_12_15_5_1_8600 88 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 271
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 87 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 91 271 (accept_3_3 86 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  91 271 (Polychromatic418967fa.accept_19_9_15_5_1_5666 85 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 91 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 271 (accept_3_3 83 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 91 271 (Polychromatic418967fa.accept_14_12_7_5_1_1107 82 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 271
  (Polychromatic418967fa.accept_11_4_3_7_1_828 81 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 91 271 (accept_3_3 80 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  91 271 (Polychromatic418967fa.accept_14_9_7_5_1_1105 79 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 91 271 (Polychromatic418967fa.accept_17_10_6_16_1_6862 78 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 271 (accept_3_3 77 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 91 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 76 91 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 271
  (Polychromatic418967fa.accept_17_7_6_16_1_2195 75 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 271 (accept_3_3 74 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 271 (Polychromatic418967fa.accept_21_10_7_19_1_9208 73 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 271 (Polychromatic418967fa.accept_14_2_7_5_1_5450 72 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 271 (accept_3_3 71 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 271 (Polychromatic418967fa.accept_11_4_3_7_1_828 70 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 271
  (Polychromatic418967fa.accept_19_12_15_5_1_8600 69 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 271 (accept_3_3 68 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 271 (Polychromatic418967fa.accept_16_3_11_15_1_1963 67 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 271 (Polychromatic418967fa.accept_19_9_15_5_1_5666 66 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 271 (accept_3_3 65 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 271 (Polychromatic418967fa.accept_21_1_7_19_1_9193 64 91
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 271
  (Polychromatic418967fa.accept_19_6_15_5_1_5697 63 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 271 (accept_3_3 62 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 271 (Polychromatic418967fa.accept_17_10_6_16_1_6862 61 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 271 (accept_3_3 59 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 271 (Polychromatic418967fa.accept_14_2_7_5_1_5450 58 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 271
  (Polychromatic418967fa.accept_21_15_7_19_1_15090 57 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 91 271 (accept_3_3 56 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 91 271 (Polychromatic418967fa.accept_16_7_11_15_1_2929 55 91 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 271 (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 91
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 271 (accept_3_3 53 91 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 52
  91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 271
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 51 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 271 (accept_3_3 50 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 271 (Polychromatic418967fa.accept_16_1_11_15_1_498 49 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 271 (Polychromatic418967fa.accept_11_4_3_7_1_828 48 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 271 (accept_3_3 47 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 271 (Polychromatic418967fa.accept_21_4_7_19_1_13687 46 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 271
  (Polychromatic418967fa.accept_25_20_16_21_1_16591 45 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 91 271 (accept_3_3 44 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 91 271 (Polychromatic418967fa.accept_11_10_3_7_1_2564 43 91 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 271 (Polychromatic418967fa.accept_16_10_11_15_1_6302 42 91
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 271 (accept_3_3 41 91 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 271 (Polychromatic418967fa.accept_14_12_7_5_1_1107
  40 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 271
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 39 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 271 (accept_3_3 38 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 271 (Polychromatic418967fa.accept_11_4_3_7_1_828 37 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 271 (accept_3_3 35 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 271 (Polychromatic418967fa.accept_21_13_7_19_1_4505 34 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 271
  (Polychromatic418967fa.accept_16_1_11_15_1_498 33 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 271 (accept_3_3 32 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 271 (Polychromatic418967fa.accept_19_12_15_5_1_8600 31 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 271 (Polychromatic418967fa.accept_14_2_7_5_1_5450 30 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 271 (accept_3_3 29 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 271
  (Polychromatic418967fa.accept_17_10_6_16_1_6862 27 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 271 (accept_3_3 26 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 271 (Polychromatic418967fa.accept_19_6_15_5_1_5697 25 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 271 (Polychromatic418967fa.accept_17_7_6_16_1_2195 24 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 271 (accept_3_3 23 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 271 (Polychromatic418967fa.accept_21_1_7_19_1_9193 22 91
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 271
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 271 (accept_3_3 20 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 271 (Polychromatic418967fa.accept_16_3_11_15_1_1963 19 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 271 (Polychromatic418967fa.accept_21_18_7_19_1_12150 18 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 271 (accept_3_3 17 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 271 (Polychromatic418967fa.accept_14_2_7_5_1_5450 16 91 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 271
  (Polychromatic418967fa.accept_11_4_3_7_1_828 15 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 271 (accept_3_3 14 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 271 (Polychromatic418967fa.accept_21_13_7_19_1_4505 13 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 271 (accept_3_3 11 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 271 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 271
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 271 (accept_3_3 8 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  271 (Polychromatic418967fa.accept_16_7_11_15_1_2929 7 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 271 (Polychromatic418967fa.accept_19_6_15_5_1_5697 6 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 271 (accept_3_3 5 91 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 91 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 271
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 271 (accept_3_3 2 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  271 (Polychromatic418967fa.accept_16_1_11_15_1_498 1 91 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 271
  (allA_succ_of_accept 89 90 271 (accept_3_3 89 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  90 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 271 (Polychromatic418967fa.accept_17_2_5_16_1_1264 87 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 271 (accept_3_3 86 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 90 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 271
  (Polychromatic418967fa.accept_19_8_14_5_1_9919 84 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 271 (accept_3_3 83 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  90 271 (Polychromatic418967fa.accept_13_4_12_11_1_5362 82 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 90 271 (accept_3_3 80 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 271 (Polychromatic418967fa.accept_13_1_12_11_1_728 79 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 78 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 90 271 (accept_3_3 77 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  90 271 (Polychromatic418967fa.accept_21_13_6_19_1_4489 76 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 90 271 (Polychromatic418967fa.accept_11_9_2_7_1_1298 75 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 271 (accept_3_3 74 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 271
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 72 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 90 271 (accept_3_3 71 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  90 271 (Polychromatic418967fa.accept_17_2_5_16_1_1264 70 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 271 (accept_3_3 68 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 271
  (Polychromatic418967fa.accept_13_1_12_11_1_728 66 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 90 271 (accept_3_3 65 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  90 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 90 271 (Polychromatic418967fa.accept_19_6_14_5_1_4339 63 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 271 (accept_3_3 62 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 90 271 (accept_3_3 59 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  90 271 (Polychromatic418967fa.accept_24_10_18_7_1_2928 58 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 271 (accept_3_3 56 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 271 (Polychromatic418967fa.accept_14_13_6_5_1_1853 55 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 271
  (Polychromatic418967fa.accept_19_16_14_5_1_9920 54 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 90 271 (accept_3_3 53 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  90 271 (Polychromatic418967fa.accept_17_1_5_16_1_5589 52 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 90 271 (Polychromatic418967fa.accept_19_13_14_5_1_8545 51 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 271 (accept_3_3 50 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 271
  (Polychromatic418967fa.accept_19_10_14_5_1_3079 48 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 90 271 (accept_3_3 47 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  90 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 271 (accept_3_3 44 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 271
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 90 271 (accept_3_3 41 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  90 271 (Polychromatic418967fa.accept_13_1_12_11_1_728 40 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 90 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 271 (accept_3_3 38 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 271 (accept_3_3 35 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  90 271 (Polychromatic418967fa.accept_20_14_10_11_1_2393 34 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 271 (accept_3_3 32 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 271 (Polychromatic418967fa.accept_11_9_2_7_1_1298 31 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 271
  (Polychromatic418967fa.accept_13_4_12_11_1_5362 30 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 271 (accept_3_3 29 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 271 (Polychromatic418967fa.accept_17_11_5_16_1_5600 28 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 271 (Polychromatic418967fa.accept_13_1_12_11_1_728 27 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 271 (accept_3_3 26 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 271
  (Polychromatic418967fa.accept_20_4_10_11_1_13827 24 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 90 271 (accept_3_3 23 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 90 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 271 (accept_3_3 20 90 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 271 (Polychromatic418967fa.accept_17_2_5_16_1_1264
  19 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 90 271 (accept_3_3 17 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  90 271 (Polychromatic418967fa.accept_19_16_14_5_1_9920 16 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 90 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 271 (accept_3_3 14 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 271
  (Polychromatic418967fa.accept_21_12_6_19_1_1871 12 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 271 (accept_3_3 11 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 271 (Polychromatic418967fa.accept_13_10_12_11_1_731 10 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 271 (accept_3_3 8 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 271 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 90 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 271
  (Polychromatic418967fa.accept_19_6_14_5_1_4339 6 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 271 (accept_3_3 5 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 90 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 90 271 (Polychromatic418967fa.accept_19_3_14_5_1_8597 3 90 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 271 (accept_3_3 2 90 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 90 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 271
  (allA_of_3_1 89 89 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 271 (allA_succ_of_accept 87 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 88 271 (accept_3_3 86 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  88 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 88 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 84 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 271 (accept_3_3 83 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 88 271 (accept_3_3 80 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  88 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 88 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 271 (accept_3_3 77 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 271 (accept_3_3 74 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 271 (Polychromatic418967fa.accept_10_3_8_1_1_182 73 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 271 (accept_3_3 71 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 271 (accept_3_3 68 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 88 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 271 (accept_3_3 65 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 88 271 (accept_3_3 62 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  88 271 (Polychromatic418967fa.accept_18_7_16_1_1_4951 61 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 88 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 271 (accept_3_3 59 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 271 (accept_3_3 56 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 271 (Polychromatic418967fa.accept_13_2_10_11_1_1276 54 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 271 (accept_3_3 53 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 271 (Polychromatic418967fa.accept_16_4_8_15_1_1113 52 88
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 271 (accept_3_3 50 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 271 (accept_3_3 47 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 271 (accept_3_3 44 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 271 (accept_3_3 41 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 271 (accept_3_3 38 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 271 (accept_3_3 35 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 271 (accept_3_3 32 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 271 (accept_3_3 29 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 271 (Polychromatic418967fa.accept_13_2_10_11_1_1276 28 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 271 (accept_3_3 26 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 271 (Polychromatic418967fa.accept_13_12_10_11_1_1279 25 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 271 (accept_3_3 23 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 271 (accept_3_3 20 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 271 (Polychromatic418967fa.accept_15_3_13_1_1_479 18 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 271 (accept_3_3 17 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 271 (accept_3_3 14 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 271 (accept_3_3 11 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 271 (accept_3_3 8 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  271 (Polychromatic418967fa.accept_16_7_8_15_1_6327 7 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 88 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 271 (accept_3_3 5 88 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 88 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 88 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 88 271 (accept_3_3 2 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88
  271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 88 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87
  271 (allA_succ_of_accept 86 87 271 (accept_3_3 86 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 87 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 84 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 271 (accept_3_3 83 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 271 (accept_3_3 80 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 79 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 271 (accept_3_3 77 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 75 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 271 (accept_3_3 74 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 271 (Polychromatic418967fa.accept_13_8_9_11_1_1265 73 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 271 (accept_3_3 71 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 271
  (Polychromatic418967fa.accept_11_3_10_7_1_129 69 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 271 (accept_3_3 68 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 271 (accept_3_3 65 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 271
  (Polychromatic418967fa.accept_19_6_11_5_1_5628 63 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 271 (accept_3_3 62 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 271 (Polychromatic418967fa.accept_13_8_9_11_1_1265 60 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 271 (accept_3_3 59 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 87 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 271 (accept_3_3 56 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 271 (Polychromatic418967fa.accept_19_17_11_5_1_7092 55 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 271 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 271 (accept_3_3 53 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 271 (accept_3_3 50 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 271 (accept_3_3 47 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 271 (accept_3_3 44 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 271 (Polychromatic418967fa.accept_17_8_2_16_1_5598 42 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 271 (accept_3_3 41 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 271 (accept_3_3 38 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 271 (accept_3_3 35 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 271 (accept_3_3 32 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 271 (accept_3_3 29 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 271
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 271 (accept_3_3 26 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 271 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 271 (accept_3_3 23 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 271 (accept_3_3 20 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 271 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 271 (Polychromatic418967fa.accept_17_1_2_16_1_5596 18 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 271 (accept_3_3 17 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 271 (accept_3_3 14 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 271 (accept_3_3 11 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 87 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 271 (accept_3_3 8 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 87 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 271 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 87 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 271 (accept_3_3 5 87 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 271 (accept_3_3 2 87 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 87
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 271
  (allA_of_3_1 86 86 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 271 (allA_succ_of_accept 84 85 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 271 (accept_3_3 83 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 271 (accept_3_3 80 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 271 (accept_3_3 77 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 271 (accept_3_3 74 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 271
  (Polychromatic418967fa.accept_19_15_9_5_1_5656 72 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 271 (accept_3_3 71 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 271 (accept_3_3 68 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 271 (accept_3_3 65 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 271 (Polychromatic418967fa.accept_10_4_5_1_1_497 64 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 271 (Polychromatic418967fa.accept_23_17_16_18_1_10062 63 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 271 (accept_3_3 62 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 85 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 271 (accept_3_3 59 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 271 (accept_3_3 56 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 271 (accept_3_3 53 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 271 (accept_3_3 50 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 271 (accept_3_3 47 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 271 (accept_3_3 44 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 271 (accept_3_3 41 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 271 (Polychromatic418967fa.accept_13_1_7_11_1_702 40 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 271 (accept_3_3 38 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 271 (Polychromatic418967fa.accept_11_4_8_7_1_819 37 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 271
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 271 (accept_3_3 35 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 271 (accept_3_3 32 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 271 (accept_3_3 29 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 271 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 271 (accept_3_3 26 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 271 (accept_3_3 23 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 271 (accept_3_3 20 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 271 (accept_3_3 17 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 271 (accept_3_3 14 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 271 (accept_3_3 11 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 271 (accept_3_3 8 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 85 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 271 (accept_3_3 5 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 85 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 85 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 271 (accept_3_3 2 85 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 271 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 85 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 271
  (allA_succ_of_accept 83 84 271 (accept_3_3 83 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 271 (Polychromatic418967fa.accept_13_4_6_11_1_2017 82 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 271 (Polychromatic418967fa.accept_15_6_9_1_1_1823 81 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 271 (accept_3_3 80 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 84 271 (accept_3_3 77 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  84 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 84 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 271 (accept_3_3 74 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 271 (Polychromatic418967fa.accept_13_8_6_11_1_1979 73 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 271
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 72 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 271 (accept_3_3 71 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 271 (accept_3_3 68 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 271
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 66 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 84 271 (accept_3_3 65 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  84 271 (Polychromatic418967fa.accept_24_16_12_7_1_13272 64 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 271 (Polychromatic418967fa.accept_22_19_18_7_1_16579 63 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 271 (accept_3_3 62 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 84 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 271 (accept_3_3 59 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 271 (accept_3_3 56 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 271 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 271
  (Polychromatic418967fa.accept_19_16_8_5_1_4322 54 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 271 (accept_3_3 53 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  84 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 271 (accept_3_3 50 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 271
  (Polychromatic418967fa.accept_19_10_8_5_1_5689 48 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 271 (accept_3_3 47 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 271 (Polychromatic418967fa.accept_16_14_4_15_1_3944 46 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 271 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 271 (accept_3_3 44 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 271 (accept_3_3 41 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 271 (Polychromatic418967fa.accept_18_3_12_1_1_3787 39 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 271 (accept_3_3 38 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 84 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 271
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 271 (accept_3_3 35 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 271 (accept_3_3 32 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 271
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 30 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 271 (accept_3_3 29 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 271 (Polychromatic418967fa.accept_16_12_4_15_1_5091 28 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 271 (accept_3_3 26 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 271 (accept_3_3 23 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 271 (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 271 (accept_3_3 20 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 84 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 271
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 271 (accept_3_3 17 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 271 (accept_3_3 14 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 271
  (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 271 (accept_3_3 11 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 271 (Polychromatic418967fa.accept_15_10_9_1_1_3688 10 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 271 (Polychromatic418967fa.accept_23_9_15_18_1_16590 9 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 271 (accept_3_3 8 84 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 84 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 271 (accept_3_3 5 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  271 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 84 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 84 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 271 (accept_3_3 2 84 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 271 (Polychromatic418967fa.accept_20_1_4_11_1_5098 1 84 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 271 (allA_of_3_1
  83 83 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 271 (allA_succ_of_accept 81 82 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 271 (accept_3_3 80 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 79 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 271 (Polychromatic418967fa.accept_22_12_16_7_1_13527 78 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 271 (accept_3_3 77 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 76 82 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 271 (accept_3_3 74 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 271 (Polychromatic418967fa.accept_13_7_4_11_1_1967 72 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 271 (accept_3_3 71 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 271 (Polychromatic418967fa.accept_15_10_7_1_1_3686 70 82
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 271 (accept_3_3 68 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 271 (Polychromatic418967fa.accept_13_2_4_11_1_2003 67 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 66 82 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 271 (accept_3_3 65 82 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 271 (Polychromatic418967fa.accept_11_9_5_7_1_815 64 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 271 (accept_3_3 62 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 271 (Polychromatic418967fa.accept_13_8_4_11_1_3469 60 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 271 (accept_3_3 59 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 271 (Polychromatic418967fa.accept_13_6_4_11_1_282 58 82 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 271 (accept_3_3 56 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 271 (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 271 (Polychromatic418967fa.accept_13_2_4_11_1_2003 54 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 271 (accept_3_3 53 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 82 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 271 (accept_3_3 50 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 271 (Polychromatic418967fa.accept_23_2_13_18_1_6781 48 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 271 (accept_3_3 47 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 82 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 271 (accept_3_3 44 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 271 (Polychromatic418967fa.accept_11_9_5_7_1_815 42 82 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 271 (accept_3_3 41 82 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 271 (accept_3_3 38 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 82 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 271 (accept_3_3 35 82 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 271 (Polychromatic418967fa.accept_13_8_4_11_1_3469 34 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 271 (accept_3_3 32 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 271 (Polychromatic418967fa.accept_11_9_5_7_1_815 31 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 271 (Polychromatic418967fa.accept_19_11_6_5_1_11299 30 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 271 (accept_3_3 29 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 82 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 271 (accept_3_3 26 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 271 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 271 (accept_3_3 23 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 271 (Polychromatic418967fa.accept_19_3_6_5_1_9947 22 82 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 271 (accept_3_3 20 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 271 (Polychromatic418967fa.accept_19_18_6_5_1_4321 18 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 271 (accept_3_3 17 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 82 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 271 (accept_3_3 14 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 271 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 271 (accept_3_3 11 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 271 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 82
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 271 (accept_3_3 8 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  271 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 82 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 82 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 271 (accept_3_3 5 82 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 82 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 82 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 82 271 (accept_3_3 2 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82
  271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 271
  (allA_succ_of_accept 80 81 271 (accept_3_3 80 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 271 (accept_3_3 77 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 75 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 271 (accept_3_3 74 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 271 (Polychromatic418967fa.accept_13_8_3_11_1_3467 73 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 271 (accept_3_3 71 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 271 (accept_3_3 68 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 271 (Polychromatic418967fa.accept_13_2_3_11_1_1287 67 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 271 (accept_3_3 65 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 271
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 271 (accept_3_3 62 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 271 (Polychromatic418967fa.accept_23_15_12_18_1_13435 61 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 271 (Polychromatic418967fa.accept_13_8_3_11_1_3467 60 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 271 (accept_3_3 59 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 271 (accept_3_3 56 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 271 (accept_3_3 53 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 271 (accept_3_3 50 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 271 (Polychromatic418967fa.accept_13_10_3_11_1_1923 49 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 271 (accept_3_3 47 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 271
  (Polychromatic418967fa.accept_21_3_18_19_1_12156 45 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 271 (accept_3_3 44 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 81 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 271 (accept_3_3 41 81 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40
  81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 271 (accept_3_3 38 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 271 (accept_3_3 35 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 271
  (Polychromatic418967fa.accept_13_7_3_11_1_280 33 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 271 (accept_3_3 32 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 271 (Polychromatic418967fa.accept_13_5_3_11_1_1288 31 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 271 (accept_3_3 29 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 271 (accept_3_3 26 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 271 (Polychromatic418967fa.accept_11_3_4_7_1_114 25 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 271 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 271 (accept_3_3 23 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 271
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 271 (accept_3_3 20 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 271 (accept_3_3 17 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 271 (accept_3_3 14 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 271 (Polychromatic418967fa.accept_17_12_13_16_1_3226 12 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 271 (accept_3_3 11 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 271 (accept_3_3 8 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  271 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 271 (accept_3_3 5 81 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 271
  (Polychromatic418967fa.accept_11_3_4_7_1_114 3 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 271 (accept_3_3 2 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 81 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 271
  (allA_of_3_1 80 80 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 271 (allA_succ_of_accept 78 79 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 271 (accept_3_3 77 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 271 (accept_3_3 74 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 271
  (Polychromatic418967fa.accept_10_2_9_1_1_185 72 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 271 (accept_3_3 71 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 271 (Polychromatic418967fa.accept_18_16_7_1_1_6332 70 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 271 (accept_3_3 68 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 66 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 271 (accept_3_3 65 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 271 (Polychromatic418967fa.accept_11_9_2_7_1_1298 64 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 271 (Polychromatic418967fa.accept_14_7_9_5_1_529 63 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 271 (accept_3_3 62 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 271 (Polychromatic418967fa.accept_13_9_1_11_1_275 61 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 271 (accept_3_3 59 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 271 (accept_3_3 56 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 271 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 271
  (Polychromatic418967fa.accept_19_16_3_5_1_5684 54 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 271 (accept_3_3 53 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 271 (accept_3_3 50 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 271 (accept_3_3 47 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 271 (accept_3_3 44 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 271 (Polychromatic418967fa.accept_21_1_16_19_1_3134 43 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 271 (accept_3_3 41 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 271 (accept_3_3 38 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 271 (Polychromatic418967fa.accept_22_15_13_7_1_13559 37 79 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 271
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 271 (accept_3_3 35 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 271 (Polychromatic418967fa.accept_13_8_1_11_1_1284 34 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 271 (accept_3_3 32 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 271 (accept_3_3 29 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 271 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 271 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 271 (accept_3_3 26 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 79 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 271 (accept_3_3 23 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 271 (accept_3_3 20 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 271 (Polychromatic418967fa.accept_22_19_13_7_1_5557 19 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 271 (accept_3_3 17 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 271 (Polychromatic418967fa.accept_13_3_1_11_1_1268 16 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 271 (accept_3_3 14 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 271 (accept_3_3 11 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 271 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 271 (accept_3_3 8 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 271 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 79 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 271 (accept_3_3 5 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 79 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 79 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 271 (accept_3_3 2 79 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 271 (Polychromatic418967fa.accept_19_1_3_5_1_3092 1 79 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 271
  (allA_succ_of_accept 77 78 271 (accept_3_3 77 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 271 (accept_3_3 74 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 271
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 72 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 271 (accept_3_3 71 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 271 (accept_3_3 68 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 271 (accept_3_3 65 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 271 (Polychromatic418967fa.accept_15_4_3_1_1_487 64 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 271 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 271 (accept_3_3 62 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 271 (accept_3_3 59 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 271 (accept_3_3 56 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 271
  (Polychromatic418967fa.accept_19_16_2_5_1_5681 54 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 271 (accept_3_3 53 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 271 (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 271 (accept_3_3 50 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 271 (accept_3_3 47 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 271 (accept_3_3 44 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 271
  (Polychromatic418967fa.accept_16_10_14_15_1_2933 42 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 78 271 (accept_3_3 41 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 78 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 78 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 78 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 271 (accept_3_3 38 78 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 271
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 271 (accept_3_3 35 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 271 (accept_3_3 32 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 271 (accept_3_3 29 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 271 (accept_3_3 26 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 271 (accept_3_3 23 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 271 (accept_3_3 20 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 271 (accept_3_3 17 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 271 (Polychromatic418967fa.accept_22_15_12_7_1_15054 15 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 271 (accept_3_3 14 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 271 (accept_3_3 11 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 271 (accept_3_3 8 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 78 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 271 (accept_3_3 5 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 78 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 78 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 271 (accept_3_3 2 78 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 271 (allA_of_3_1 77 77
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 271 (allA_succ_of_accept 75 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 271 (accept_3_3 74 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 271 (Polychromatic418967fa.accept_25_23_1_21_1_16589 73 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 271 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 271 (accept_3_3 71 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 271 (accept_3_3 68 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 271 (accept_3_3 65 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 271 (accept_3_3 62 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 271 (accept_3_3 59 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 271 (Polychromatic418967fa.accept_11_3_10_7_1_129 58 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 271 (accept_3_3 56 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 271 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 271 (Polychromatic418967fa.accept_25_4_1_21_1_14802 54 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 271 (accept_3_3 53 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 76 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 271 (accept_3_3 50 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 271 (Polychromatic418967fa.accept_21_7_13_19_1_4477 49 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 271 (accept_3_3 47 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 271 (accept_3_3 44 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 271 (accept_3_3 41 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 271 (Polychromatic418967fa.accept_16_8_12_15_1_2005 40 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 271 (accept_3_3 38 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 271 (accept_3_3 35 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 271 (accept_3_3 32 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 271 (Polychromatic418967fa.accept_17_14_8_16_1_6863 31 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 271 (accept_3_3 29 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 271 (Polychromatic418967fa.accept_21_7_13_19_1_4477 28 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 271 (accept_3_3 26 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 271 (accept_3_3 23 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 271 (accept_3_3 20 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 271 (accept_3_3 17 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 271 (accept_3_3 14 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 271 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 271 (accept_3_3 11 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 76 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 271 (accept_3_3 8 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 76 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 271 (accept_3_3 5 76 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 76 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 271 (accept_3_3 2 76 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 76
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 271 (allA_succ_of_accept
  74 75 271 (accept_3_3 74 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 271
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 73 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 271 (Polychromatic418967fa.accept_21_9_12_19_1_12172 72 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 271 (accept_3_3 71 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 69
  75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 271 (accept_3_3 68 75
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 271
  (Polychromatic418967fa.accept_9_4_3_1_1_154 67 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 75 271 (Polychromatic418967fa.accept_10_6_5_1_1_482 66 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 271 (accept_3_3 65 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 271 (Polychromatic418967fa.accept_18_9_3_1_1_2559
  63 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 271 (accept_3_3 62
  75 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 271
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 75 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 271 (accept_3_3 59 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 271 (Polychromatic418967fa.accept_11_2_9_7_1_124
  57 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 271 (accept_3_3 56
  75 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 271
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 55 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 75 271 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 271 (accept_3_3 53 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 51
  75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 271 (accept_3_3 50 75
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 271
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 75 271 (Polychromatic418967fa.accept_18_12_3_1_1_3685 48 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 271 (accept_3_3 47 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 271 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 271 (accept_3_3 44
  75 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 271
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 271 (accept_3_3 41 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  39 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 271 (accept_3_3 38
  75 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 271
  (Polychromatic418967fa.accept_17_3_7_16_1_3251 37 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 75 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 271 (accept_3_3 35 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 33
  75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 271 (accept_3_3 32 75
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 271
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 75 271 (Polychromatic418967fa.accept_13_4_10_11_1_1908 30 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 271 (accept_3_3 29 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 271 (Polychromatic418967fa.accept_11_5_9_7_1_411
  27 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 271 (accept_3_3 26
  75 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 271
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 75 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 271 (accept_3_3 23 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 271 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 271 (accept_3_3 20
  75 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 271
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 75 271 (Polychromatic418967fa.accept_21_18_12_19_1_10725 18 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 271 (accept_3_3 17 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 271 (accept_3_3 14 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 271 (accept_3_3 11 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 75 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 271
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 271 (accept_3_3 8 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 271 (accept_3_3 5 75 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 271 (Polychromatic418967fa.accept_13_3_10_11_1_1293
  3 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 271 (accept_3_3 2 75
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 271
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 75 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 271
  (allA_of_3_1 74 74 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 271 (allA_succ_of_accept 72 73 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 72 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 271 (accept_3_3 71 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 271 (Polychromatic418967fa.accept_13_4_8_11_1_1937 69 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 271 (accept_3_3 68 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 271 (Polychromatic418967fa.accept_19_10_16_5_1_8562 67 73
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 271 (accept_3_3 65 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 271 (Polychromatic418967fa.accept_15_3_13_1_1_479 63 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 271 (accept_3_3 62 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 271 (Polychromatic418967fa.accept_13_9_8_11_1_725 61 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 271
  (Polychromatic418967fa.accept_19_3_16_5_1_7098 60 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 271 (accept_3_3 59 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 271 (accept_3_3 56 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 271 (Polychromatic418967fa.accept_13_3_8_11_1_1906 55 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 271 (accept_3_3 53 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 271 (Polychromatic418967fa.accept_10_2_3_1_1_481 52 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 271 (accept_3_3 50 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 271 (Polychromatic418967fa.accept_13_10_8_11_1_1985 49 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 271
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 271 (accept_3_3 47 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 271 (Polychromatic418967fa.accept_13_6_8_11_1_5398 45 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 271 (accept_3_3 44 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 73 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 271 (accept_3_3 41 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 271 (Polychromatic418967fa.accept_13_1_8_11_1_724 40 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 271 (Polychromatic418967fa.accept_19_1_16_5_1_5671 39 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 271 (accept_3_3 38 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 73 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 271 (accept_3_3 35 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 271 (Polychromatic418967fa.accept_15_3_13_1_1_479 33 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 271 (accept_3_3 32 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 271 (Polychromatic418967fa.accept_19_12_16_5_1_12620 31 73 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 271 (accept_3_3 29 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 271 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 271 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 271 (accept_3_3 26 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 271 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 271
  (Polychromatic418967fa.accept_16_8_9_15_1_5112 24 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 271 (accept_3_3 23 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 271 (Polychromatic418967fa.accept_17_4_5_16_1_3240 21 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 271 (accept_3_3 20 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 271 (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 73
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 271 (accept_3_3 17 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 271 (accept_3_3 14 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 271 (Polychromatic418967fa.accept_24_13_1_7_1_8147 13 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 271
  (Polychromatic418967fa.accept_10_2_3_1_1_481 12 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 271 (accept_3_3 11 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 271 (accept_3_3 8 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 271 (Polychromatic418967fa.accept_21_7_10_19_1_10739 7 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 271 (accept_3_3 5 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  271 (Polychromatic418967fa.accept_13_4_8_11_1_1937 4 73 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 271 (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 271 (accept_3_3 2 73 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 271 (allA_succ_of_accept 71
  72 271 (accept_3_3 71 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 271
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 70 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 72 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 271 (accept_3_3 68 72 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 66
  72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 271 (accept_3_3 65 72
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 271
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 64 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 72 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 72 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 271 (accept_3_3 62 72 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 72 271 (Polychromatic418967fa.accept_13_9_7_11_1_1292 61 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 271 (accept_3_3 59 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  72 271 (Polychromatic418967fa.accept_15_13_12_1_1_1841 58 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 271 (Polychromatic418967fa.accept_13_5_7_11_1_3470 57 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 271 (accept_3_3 56 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 271 (Polychromatic418967fa.accept_13_3_7_11_1_1904 55 72
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 271
  (Polychromatic418967fa.accept_17_3_4_16_1_3208 54 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 72 271 (accept_3_3 53 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  72 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 271 (Polychromatic418967fa.accept_13_12_7_11_1_1935 51 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 271 (accept_3_3 50 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 72 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 271
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 48 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 271 (accept_3_3 47 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 271 (accept_3_3 44 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 271
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 42 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 271 (accept_3_3 41 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 271 (Polychromatic418967fa.accept_13_1_7_11_1_702 40 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 271 (accept_3_3 38 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 271 (Polychromatic418967fa.accept_17_3_4_16_1_3208 37 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 271
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 271 (accept_3_3 35 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 271 (Polychromatic418967fa.accept_11_1_6_7_1_116 34 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 271 (accept_3_3 32 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 271
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 30 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 271 (accept_3_3 29 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 271 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 271 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 271 (accept_3_3 26 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 271 (accept_3_3 23 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 271 (Polychromatic418967fa.accept_13_9_7_11_1_1292 22 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 271 (Polychromatic418967fa.accept_14_7_2_5_1_4528 21 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 271 (accept_3_3 20 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 271 (accept_3_3 17 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 271 (Polychromatic418967fa.accept_17_15_4_16_1_6890 15 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 271 (accept_3_3 14 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 72 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 271
  (Polychromatic418967fa.accept_11_1_6_7_1_116 12 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 271 (accept_3_3 11 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 271 (accept_3_3 8 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 271 (Polychromatic418967fa.accept_14_7_2_5_1_4528 7 72 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 271
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 271 (accept_3_3 5 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 72 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 72 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 271 (accept_3_3 2 72 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 72 271 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 72 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 271 (allA_of_3_1 71 71 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 271 (allA_succ_of_accept 69 70 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 271 (accept_3_3 68 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 271 (accept_3_3 65 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 271 (accept_3_3 62 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 271 (accept_3_3 59 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 271 (accept_3_3 56 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 271 (Polychromatic418967fa.accept_13_3_5_11_1_716 55 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 271 (Polychromatic418967fa.accept_15_9_10_1_1_1062 54 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 271 (accept_3_3 53 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303 52 70 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 271 (accept_3_3 50 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 271 (accept_3_3 47 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 271 (Polychromatic418967fa.accept_13_7_5_11_1_1927 46 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 271 (accept_3_3 44 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 271 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 271 (accept_3_3 41 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 271 (accept_3_3 38 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 271 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 271 (accept_3_3 35 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 271 (Polychromatic418967fa.accept_20_14_10_11_1_2393 34 70 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 271 (accept_3_3 32 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 271 (accept_3_3 29 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 271 (accept_3_3 26 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 271 (accept_3_3 23 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 271 (accept_3_3 20 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 271 (Polychromatic418967fa.accept_17_1_2_16_1_5596 18 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 271 (accept_3_3 17 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 70 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 271 (accept_3_3 14 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 271 (accept_3_3 11 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 271 (Polychromatic418967fa.accept_18_10_16_1_1_1534 10 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 271 (accept_3_3 8 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  271 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 70 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 271 (accept_3_3 5 70 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 70 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 271 (accept_3_3 2 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 271
  (allA_succ_of_accept 68 69 271 (accept_3_3 68 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 271 (accept_3_3 65 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 271 (accept_3_3 62 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 271 (accept_3_3 59 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 271 (accept_3_3 56 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 271 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 271 (accept_3_3 53 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 271 (accept_3_3 50 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 271 (accept_3_3 47 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 271
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 271 (accept_3_3 44 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 271 (accept_3_3 41 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 271 (accept_3_3 38 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 271 (Polychromatic418967fa.accept_11_4_3_7_1_828 37 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 271 (accept_3_3 35 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 271
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 271 (accept_3_3 32 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 271 (accept_3_3 29 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 271 (accept_3_3 26 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 271 (Polychromatic418967fa.accept_21_3_6_19_1_3125 24 69 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 271 (accept_3_3 23 69 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 271 (accept_3_3 20 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 271 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 271 (accept_3_3 17 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 271 (accept_3_3 14 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 271 (accept_3_3 11 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 271
  (Polychromatic418967fa.accept_19_9_12_5_1_5695 9 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 271 (accept_3_3 8 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 69 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 271 (accept_3_3 5 69 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 69
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 271 (accept_3_3 2 69 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 69
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 271 (allA_of_3_1 68 68 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 271 (allA_succ_of_accept 66 67 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 271 (accept_3_3 65 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 271 (Polychromatic418967fa.accept_24_15_19_7_1_13255 63 67 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 271 (accept_3_3 62 67 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 67 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 271
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 271 (accept_3_3 59 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 271 (accept_3_3 56 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 67 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 271
  (Polychromatic418967fa.accept_10_4_7_1_1_471 54 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 271 (accept_3_3 53 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 271 (accept_3_3 50 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 271 (Polychromatic418967fa.accept_13_10_2_11_1_1920 49 67 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 271 (accept_3_3 47 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 271 (Polychromatic418967fa.accept_10_6_7_1_1_1297 46 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 271 (Polychromatic418967fa.accept_16_13_3_15_1_1931 45 67 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 271 (accept_3_3 44 67 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 67 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 271 (accept_3_3 41 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 271 (Polychromatic418967fa.accept_15_10_7_1_1_3686 40 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 271 (accept_3_3 38 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 67 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 271 (accept_3_3 35 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 271 (accept_3_3 32 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 271 (Polychromatic418967fa.accept_21_10_4_19_1_3136 31 67 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 271 (accept_3_3 29 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 271 (accept_3_3 26 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 271 (accept_3_3 23 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 271 (accept_3_3 20 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 271 (Polychromatic418967fa.accept_27_19_13_1_1_16588 19 67 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 271
  (Polychromatic418967fa.accept_16_2_3_15_1_6309 18 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 271 (accept_3_3 17 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 271 (accept_3_3 14 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 67 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 271
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 271 (accept_3_3 11 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 271 (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 271 (accept_3_3 8 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 271 (accept_3_3 5 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  271 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 67 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 67 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 271 (accept_3_3 2 67 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 67 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 271 (allA_succ_of_accept 65 66
  271 (accept_3_3 65 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 64 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 271 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 66 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 271 (accept_3_3 62 66 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 60
  66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 271 (accept_3_3 59 66
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 271 (Polychromatic418967fa.accept_7_2_3_5_1_34
  58 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 66 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 66 271 (accept_3_3 56 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  66 271 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 66 271 (Polychromatic418967fa.accept_14_12_10_5_1_2712 54 66 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 271 (accept_3_3 53 66 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 66 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 66 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 66 271 (accept_3_3 50 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  66 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 66 271 (Polychromatic418967fa.accept_13_9_1_11_1_275 48 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 271 (accept_3_3 47 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 271 (Polychromatic418967fa.accept_13_7_1_11_1_732 46 66 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 66 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 66 271 (accept_3_3 44 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  66 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 66 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 271 (accept_3_3 41 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 66 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 271
  (Polychromatic418967fa.accept_15_9_6_1_1_493 39 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 66 271 (accept_3_3 38 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  66 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 66 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 271 (accept_3_3 35 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 66 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 66 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 66 271 (accept_3_3 32 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  66 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 66 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 271 (accept_3_3 29 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 271 (Polychromatic418967fa.accept_16_12_2_15_1_490 28 66 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 271
  (Polychromatic418967fa.accept_10_7_6_1_1_486 27 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 66 271 (accept_3_3 26 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  66 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 66 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 271 (accept_3_3 23 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 66 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 66 271 (accept_3_3 20 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  66 271 (Polychromatic418967fa.accept_16_3_2_15_1_7367 19 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 66 271 (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 271 (accept_3_3 17 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 66 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 271 (accept_3_3 14 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  66 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 271 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 271 (accept_3_3 11 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 271 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 66 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 271 (accept_3_3 8 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66
  271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 66 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 271 (accept_3_3 5 66 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 66 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 271 (Polychromatic418967fa.accept_13_3_1_11_1_1268
  3 66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 271 (accept_3_3 2 66
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  66 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 271 (allA_of_3_1 65 65 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 271 (allA_succ_of_accept 63 64 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 271 (accept_3_3 62 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 271 (Polychromatic418967fa.accept_20_1_4_11_1_5098 61 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 64 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 271 (accept_3_3 59 64 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 271 (accept_3_3 56 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 271 (Polychromatic418967fa.accept_17_3_13_16_1_2183 54 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 271 (accept_3_3 53 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 64 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 271 (accept_3_3 50 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 271 (Polychromatic418967fa.accept_11_5_9_7_1_411 49 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 64 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 271 (accept_3_3 47 64 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 271 (accept_3_3 44 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 271 (Polychromatic418967fa.accept_13_4_12_11_1_5362 43 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 271 (Polychromatic418967fa.accept_15_12_4_1_1_3746 42 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 271 (accept_3_3 41 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 271 (Polychromatic418967fa.accept_13_1_12_11_1_728 40 64
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 271 (accept_3_3 38 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 271 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 271 (accept_3_3 35 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 64 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 271 (accept_3_3 32 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 271 (Polychromatic418967fa.accept_13_4_12_11_1_5362 30 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 271 (accept_3_3 29 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 271 (Polychromatic418967fa.accept_19_9_7_5_1_9887 28 64 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 271 (accept_3_3 26 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 64 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 271 (accept_3_3 23 64 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 271 (accept_3_3 20 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 271 (Polychromatic418967fa.accept_25_19_14_21_1_14788 19 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 64 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 271 (accept_3_3 17 64 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 271 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 271 (accept_3_3 14 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 271 (Polychromatic418967fa.accept_15_12_4_1_1_3746 12 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 271 (accept_3_3 11 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 64 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 271 (accept_3_3 8 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 64 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 64 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 271 (accept_3_3 5 64 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 64 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 271 (accept_3_3 2 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  271 (Polychromatic418967fa.accept_13_1_12_11_1_728 1 64 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 64 271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 271
  (allA_succ_of_accept 62 63 271 (accept_3_3 62 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 271 (Polychromatic418967fa.accept_19_4_6_5_1_11350 61 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 271 (Polychromatic418967fa.accept_18_6_9_1_1_3769 60 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 271 (accept_3_3 59 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 63 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 271 (accept_3_3 56 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 271 (Polychromatic418967fa.accept_23_9_17_18_1_16587 55 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 271 (Polychromatic418967fa.accept_14_12_7_5_1_1107 54 63 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 271 (accept_3_3 53 63 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 271
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 51 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 271 (accept_3_3 50 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 271 (Polychromatic418967fa.accept_15_4_3_1_1_487 49 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 271 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 271 (accept_3_3 47 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 63 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 271 (accept_3_3 44 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 271 (Polychromatic418967fa.accept_15_13_3_1_1_3740 43 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 271 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 271 (accept_3_3 41 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 271
  (Polychromatic418967fa.accept_18_3_9_1_1_3690 39 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 271 (accept_3_3 38 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 271 (Polychromatic418967fa.accept_11_4_8_7_1_819 37 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 271 (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 271 (accept_3_3 35 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 271 (accept_3_3 32 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 271 (Polychromatic418967fa.accept_25_6_13_21_1_16586 31 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 271 (Polychromatic418967fa.accept_14_2_7_5_1_5450 30 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 271 (accept_3_3 29 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 271
  (Polychromatic418967fa.accept_28_27_7_19_1_12683 27 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 63 271 (accept_3_3 26 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 271 (Polychromatic418967fa.accept_22_3_19_7_1_8857 25 63 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 271 (Polychromatic418967fa.accept_18_6_9_1_1_3769 24 63 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 271 (accept_3_3 23 63 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 271 (accept_3_3 20 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 271 (Polychromatic418967fa.accept_15_4_3_1_1_487 19 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 271 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 271 (accept_3_3 17 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 271
  (Polychromatic418967fa.accept_11_4_8_7_1_819 15 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 271 (accept_3_3 14 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 271 (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 271 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 271 (accept_3_3 11 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 63 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 271 (accept_3_3 8 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  271 (Polychromatic418967fa.accept_19_7_6_5_1_4320 7 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 271 (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 271 (accept_3_3 5 63 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 271
  (Polychromatic418967fa.accept_18_3_9_1_1_3690 3 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 271 (accept_3_3 2 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  271 (Polychromatic418967fa.accept_17_1_12_16_1_2211 1 63 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 271
  (allA_of_3_1 62 62 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 271 (allA_succ_of_accept 60 61 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 271 (accept_3_3 59 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 271 (accept_3_3 56 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 271 (Polychromatic418967fa.accept_22_11_17_7_1_5448 55 61 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 271 (accept_3_3 53 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 271 (Polychromatic418967fa.accept_18_16_7_1_1_6332 52 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 271 (accept_3_3 50 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 61 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 271 (accept_3_3 47 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 271 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 271 (accept_3_3 44 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 271 (Polychromatic418967fa.accept_17_9_10_16_1_3217 43 61 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 271 (accept_3_3 41 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 271 (accept_3_3 38 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 271 (Polychromatic418967fa.accept_19_18_4_5_1_5723 37 61 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 271
  (Polychromatic418967fa.accept_20_16_1_11_1_9647 36 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 271 (accept_3_3 35 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 271 (accept_3_3 32 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 61 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 271 (accept_3_3 29 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 271 (Polychromatic418967fa.accept_13_2_9_11_1_258 28 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 271 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 271 (accept_3_3 26 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 271 (Polychromatic418967fa.accept_19_6_4_5_1_5650 25 61 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 271 (accept_3_3 23 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 271 (accept_3_3 20 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 271 (Polychromatic418967fa.accept_16_3_13_15_1_1913 19 61 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 271 (accept_3_3 17 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 271 (Polychromatic418967fa.accept_18_16_7_1_1_6332 16 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 271 (accept_3_3 14 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 61 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 271 (accept_3_3 11 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 271 (Polychromatic418967fa.accept_17_9_10_16_1_3217 9 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 271 (accept_3_3 8 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 271 (Polychromatic418967fa.accept_13_7_9_11_1_705 7 61 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 271 (accept_3_3 5 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  271 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 61 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 61 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 271 (accept_3_3 2 61 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 271 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 61 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 271 (allA_succ_of_accept 59 60 271 (accept_3_3 59 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 60 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 271 (accept_3_3 56 60 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 55
  60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 271
  (Polychromatic418967fa.accept_19_16_3_5_1_5684 54 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 271 (accept_3_3 53 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 271 (accept_3_3 50 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 60 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 271 (accept_3_3 47 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 271 (Polychromatic418967fa.accept_19_8_3_5_1_11324 46 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 271 (Polychromatic418967fa.accept_13_6_8_11_1_5398 45 60 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 271 (accept_3_3 44 60 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 60 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 271
  (Polychromatic418967fa.accept_11_9_5_7_1_815 42 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 271 (accept_3_3 41 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  60 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 271 (accept_3_3 38 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 60 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 271 (accept_3_3 35 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 271 (Polychromatic418967fa.accept_19_14_3_5_1_11347 33 60 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 271 (accept_3_3 32 60 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 60 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 271 (accept_3_3 29 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 271 (Polychromatic418967fa.accept_21_7_18_19_1_10715 28 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 271 (accept_3_3 26 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 60 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 271
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 24 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 271 (accept_3_3 23 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 271 (accept_3_3 20 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 60 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 271
  (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 271 (accept_3_3 17 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 271 (accept_3_3 14 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 271 (accept_3_3 11 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 271 (Polychromatic418967fa.accept_13_10_8_11_1_1985 10 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 271 (accept_3_3 8 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 271 (accept_3_3 5 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  271 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 60 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 60 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 271 (accept_3_3 2 60 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 271 (allA_of_3_1 59 59 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 271
  (allA_succ_of_accept 57 58 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 271 (accept_3_3 56 58 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 271 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 58 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 271
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 58 271 (accept_3_3 53 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  58 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 58 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 271 (accept_3_3 50 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 58 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 58 271 (accept_3_3 47 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 271 (accept_3_3 44 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 58 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 271 (accept_3_3 41 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 271 (accept_3_3 38 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 271
  (Polychromatic418967fa.accept_20_16_18_11_1_9605 36 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 58 271 (accept_3_3 35 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 58 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 58 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 271 (accept_3_3 32 58 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 31
  58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 271 (accept_3_3 29 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 271 (accept_3_3 26 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 271 (accept_3_3 23 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 271 (Polychromatic418967fa.accept_19_3_1_5_1_8549 22 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 271 (accept_3_3 20 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 58 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 271 (accept_3_3 17 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 271 (accept_3_3 14 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 271 (accept_3_3 11 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 271 (accept_3_3 8 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 58 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 271 (accept_3_3 5 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 58 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 271 (accept_3_3 2 58 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 57 271 (allA_succ_of_accept 56 57 271 (accept_3_3 56 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 57 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 57 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 271 (accept_3_3 53 57 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52
  57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 271 (accept_3_3 50 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  57 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 271 (accept_3_3 47 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 57 271 (accept_3_3 44 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  57 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 57 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 271 (accept_3_3 41 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 57 271 (accept_3_3 38 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  57 271 (Polychromatic418967fa.accept_22_15_13_7_1_13559 37 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 57 271 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 271 (accept_3_3 35 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 271 (accept_3_3 32 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  57 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 271 (accept_3_3 29 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 271 (accept_3_3 26 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  57 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 271 (accept_3_3 23 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 271
  (Polychromatic418967fa.accept_20_1_17_11_1_8119 21 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 271 (accept_3_3 20 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 271 (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 271 (accept_3_3 17 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 271 (accept_3_3 14 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 271 (Polychromatic418967fa.accept_18_12_3_1_1_3685 12 57 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 271 (accept_3_3 11 57 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 271
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 271 (accept_3_3 8 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 57 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 271 (accept_3_3 5 57 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 57 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 57
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 271 (accept_3_3 2 57 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 271 (Polychromatic418967fa.accept_20_1_17_11_1_8119
  1 57 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 271 (allA_of_3_1 56 56 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 55 271 (allA_succ_of_accept 54 55 271
  (Polychromatic418967fa.accept_10_4_5_1_1_497 54 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 271 (accept_3_3 53 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 271 (Polychromatic418967fa.accept_15_7_10_1_1_1836 52 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 271 (Polychromatic418967fa.accept_15_6_10_1_1_3675 51 55 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 271 (accept_3_3 50 55 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 55 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 271
  (Polychromatic418967fa.accept_14_6_13_5_1_534 48 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 271 (accept_3_3 47 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 271 (Polychromatic418967fa.accept_19_7_17_5_1_3081 45 55 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 271 (accept_3_3 44 55 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 55 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 271
  (Polychromatic418967fa.accept_28_14_27_19_1_16585 42 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 55 271 (accept_3_3 41 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 55 271 (Polychromatic418967fa.accept_13_1_3_11_1_1289 40 55 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 55 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 271 (accept_3_3 38 55 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 271 (Polychromatic418967fa.accept_15_7_10_1_1_1836
  37 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 271 (accept_3_3 35 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 271 (Polychromatic418967fa.accept_10_4_5_1_1_497 34 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 271 (Polychromatic418967fa.accept_13_7_3_11_1_280 33 55 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 271 (accept_3_3 32 55 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 271 (Polychromatic418967fa.accept_13_5_3_11_1_1288 31 55 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 271
  (Polychromatic418967fa.accept_16_14_7_15_1_3947 30 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 271 (accept_3_3 29 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 271 (Polychromatic418967fa.accept_13_2_3_11_1_1287 28 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 271 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 55 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 271 (accept_3_3 26 55 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 55 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 271
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 271 (accept_3_3 23 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 271 (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 55 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 271 (accept_3_3 20 55 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 55 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 271 (accept_3_3 17 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 271 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 55 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 271 (accept_3_3 14 55 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 271 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 55 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 271
  (Polychromatic418967fa.accept_19_12_17_5_1_5702 12 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 271 (accept_3_3 11 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 271 (Polychromatic418967fa.accept_13_10_3_11_1_1923 10 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 55 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 271 (accept_3_3 8 55 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 271 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 55 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 271
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 271 (accept_3_3 5 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 55 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 271 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 55 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 271 (accept_3_3 2 55 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 55 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 271)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 271 (allA_succ_of_accept 53 54 271 (accept_3_3 53 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 271 (Polychromatic418967fa.accept_14_10_12_5_1_3466 52 54 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 54 271 (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 54 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 271 (accept_3_3 50 54 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 271
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 48 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 271 (accept_3_3 47 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 271 (Polychromatic418967fa.accept_19_8_16_5_1_8583 46 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 271 (accept_3_3 44 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 271 (Polychromatic418967fa.accept_13_4_2_11_1_733 43 54 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 271
  (Polychromatic418967fa.accept_13_3_2_11_1_1999 42 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 271 (accept_3_3 41 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 271 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 271 (Polychromatic418967fa.accept_16_7_6_15_1_495 39 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 271 (accept_3_3 38 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 271
  (Polychromatic418967fa.accept_11_3_10_7_1_129 36 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 271 (accept_3_3 35 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 271 (Polychromatic418967fa.accept_22_12_10_7_1_2604 34 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 271 (accept_3_3 32 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 271 (Polychromatic418967fa.accept_14_3_12_5_1_153 31 54 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 271
  (Polychromatic418967fa.accept_13_4_2_11_1_733 30 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 271 (accept_3_3 29 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 271 (Polychromatic418967fa.accept_21_7_12_19_1_10712 28 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 271 (accept_3_3 26 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 271
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 271 (accept_3_3 23 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 271 (Polychromatic418967fa.accept_13_9_2_11_1_1964 22 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 271 (accept_3_3 20 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 271 (Polychromatic418967fa.accept_22_19_10_7_1_8849 19 54 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 271
  (Polychromatic418967fa.accept_21_18_12_19_1_10725 18 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 271 (accept_3_3 17 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 271 (Polychromatic418967fa.accept_13_3_2_11_1_1999 16 54 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 271 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 54 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 271 (accept_3_3 14 54 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 271
  (Polychromatic418967fa.accept_19_12_16_5_1_12620 12 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 271 (accept_3_3 11 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 271 (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 54 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 271 (accept_3_3 8 54 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7
  54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 271
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 271 (accept_3_3 5 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  271 (Polychromatic418967fa.accept_13_4_2_11_1_733 4 54 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 271 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 271 (accept_3_3 2 54 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 271 (allA_of_3_1 53 53 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 271 (allA_succ_of_accept 51 52 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 271 (accept_3_3 50 52 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 49
  52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 271 (accept_3_3 47 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 271 (accept_3_3 44 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 52 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 271 (accept_3_3 41 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 271 (accept_3_3 38 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 52 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 271 (accept_3_3 35 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 271 (accept_3_3 32 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 271 (accept_3_3 29 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 271 (Polychromatic418967fa.accept_16_12_4_15_1_5091 28 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 271 (accept_3_3 26 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 271 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 52 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 271 (accept_3_3 23 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 271 (accept_3_3 20 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 52 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 271
  (Polychromatic418967fa.accept_22_18_8_7_1_11987 18 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 271 (accept_3_3 17 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 271 (accept_3_3 14 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 52 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 271 (accept_3_3 11 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 271 (accept_3_3 8 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 271 (Polychromatic418967fa.accept_18_7_16_1_1_4951 7 52 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 271 (accept_3_3 5 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  271 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 52 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 271 (accept_3_3 2 52 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 52 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 271))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 271 (allA_succ_of_accept 50 51 271 (accept_3_3 50 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 51 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 51 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 271 (accept_3_3 47 51 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 271 (accept_3_3 44 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 271 (Polychromatic418967fa.accept_25_17_1_21_1_16584 42 51 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 271 (accept_3_3 41 51 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 271 (accept_3_3 38 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 271 (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 51 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 271 (accept_3_3 35 51 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 271 (accept_3_3 32 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 51 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 271 (accept_3_3 29 51 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 271
  (Polychromatic418967fa.accept_13_1_12_11_1_728 27 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 271 (accept_3_3 26 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 271 (accept_3_3 23 51 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 271 (accept_3_3 20 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 271 (Polychromatic418967fa.accept_24_19_3_7_1_13315 19 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 51 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 271 (accept_3_3 17 51 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 271
  (Polychromatic418967fa.accept_21_15_9_19_1_10768 15 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 51 271 (accept_3_3 14 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 51 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 51 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 271 (accept_3_3 11 51 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10
  51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 271 (accept_3_3 8 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 271 (Polychromatic418967fa.accept_23_6_5_18_1_16576 6 51 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 271 (accept_3_3 5 51 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 271 (accept_3_3 2 51 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 271 (Polychromatic418967fa.accept_13_1_12_11_1_728
  1 51 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  271))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 271 (allA_of_3_1 50 50 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 271 (allA_succ_of_accept 48 49 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 271 (accept_3_3 47 49 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 271
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 271 (accept_3_3 44 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 271 (accept_3_3 41 49 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 271 (Polychromatic418967fa.accept_13_1_10_11_1_1280 40 49 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 271 (accept_3_3 38 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 271 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 271 (Polychromatic418967fa.accept_19_17_11_5_1_7092 36 49 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 271 (accept_3_3 35 49 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 271 (accept_3_3 32 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 271 (Polychromatic418967fa.accept_11_9_5_7_1_815 31 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 271 (accept_3_3 29 49 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 271 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 49 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 271
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 271 (accept_3_3 26 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 271 (accept_3_3 23 49 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 271 (accept_3_3 20 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 271 (Polychromatic418967fa.accept_24_19_1_7_1_9846 19 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 271 (accept_3_3 17 49 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 271 (accept_3_3 14 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 271 (Polychromatic418967fa.accept_19_13_11_5_1_5692 13 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 271 (accept_3_3 11 49 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 271
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 271 (accept_3_3 8 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 271 (accept_3_3 5 49 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 271 (Polychromatic418967fa.accept_13_4_10_11_1_1908 4 49 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 49
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 271 (accept_3_3 2 49 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 271 (Polychromatic418967fa.accept_13_1_10_11_1_1280
  1 49 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  271))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 271 (allA_succ_of_accept 47 48 271 (accept_3_3 47
  48 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 46 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 271 (Polychromatic418967fa.accept_17_11_14_16_1_1270 45 48 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 271 (accept_3_3 44 48 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 48 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 42
  48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 271 (accept_3_3 41 48
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 271
  (Polychromatic418967fa.accept_9_4_3_1_1_154 40 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 48 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 271 (accept_3_3 38 48 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 48 271 (Polychromatic418967fa.accept_19_18_10_5_1_12639 37 48 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 271 (accept_3_3 35 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 48 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 271 (accept_3_3 32 48 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 48 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 271
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 271 (accept_3_3 29 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 271 (Polychromatic418967fa.accept_13_2_9_11_1_258 28 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 271 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 48 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 271 (accept_3_3 26 48 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 271 (accept_3_3 23 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 271 (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 48 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 271 (accept_3_3 20 48 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 48 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 271 (accept_3_3 17 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 271 (accept_3_3 14 48 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 271
  (Polychromatic418967fa.accept_21_12_6_19_1_1871 12 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 271 (accept_3_3 11 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 271 (Polychromatic418967fa.accept_22_10_4_7_1_16583 10 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 48 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 271 (accept_3_3 8 48 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 271 (accept_3_3 5 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 48 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 271 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 48 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 271 (accept_3_3 2 48 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 271)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 271 (allA_of_3_1 47 47 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 271 (allA_succ_of_accept 45 46
  271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 271 (accept_3_3 44 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 271 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 46 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 271 (accept_3_3 41 46 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 46 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 271 (accept_3_3 38 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 46 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 271 (accept_3_3 35 46 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 46 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 271 (accept_3_3 32 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 271 (Polychromatic418967fa.accept_11_9_2_7_1_1298 31 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 46 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 271 (accept_3_3 29 46 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 46 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 271 (accept_3_3 26 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 271 (Polychromatic418967fa.accept_33_24_13_7_1_16582 24 46 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 271 (accept_3_3 23 46 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 46 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 271 (accept_3_3 20 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 271 (Polychromatic418967fa.accept_24_19_22_7_1_8111 19 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 271 (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 46 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 271 (accept_3_3 17 46 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 46 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 271 (accept_3_3 14 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 271 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 46 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 271 (accept_3_3 11 46 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 271 (Polychromatic418967fa.accept_16_10_14_15_1_2933 10 46 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 271 (accept_3_3 8 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  271 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 46 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 46 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 271 (accept_3_3 5 46 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 46 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 271 (accept_3_3 2 46 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  271)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 271 (allA_succ_of_accept 44 45 271 (accept_3_3 44 45
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 271 (Polychromatic418967fa.accept_7_1_3_5_1_33
  43 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 271 (accept_3_3 41 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  45 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 45 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 271 (accept_3_3 38 45 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 45 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 271 (accept_3_3 35 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 271 (Polychromatic418967fa.accept_22_11_1_7_1_16581 33 45 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 271 (accept_3_3 32 45 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 271 (Polychromatic418967fa.accept_13_5_6_11_1_1933 31 45
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 271 (accept_3_3 29 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 45 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 271 (accept_3_3 26 45 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 271 (Polychromatic418967fa.accept_19_6_7_5_1_256 25 45 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 271
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 271 (accept_3_3 23 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 271 (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 45 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 271 (accept_3_3 20 45 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 45 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 271 (accept_3_3 17 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 45 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 271 (accept_3_3 14 45 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 271 (Polychromatic418967fa.accept_19_13_7_5_1_5712 13 45 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 271
  (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 271 (accept_3_3 11 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 271 (accept_3_3 8 45 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 271 (Polychromatic418967fa.accept_25_7_20_21_1_16580 7 45 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 271 (accept_3_3 5 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 45 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 271 (accept_3_3 2 45 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 45 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 271))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  271 (allA_of_3_1 44 44 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 271 (allA_succ_of_accept 42 43 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 271 (accept_3_3 41 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 271 (accept_3_3 38 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 271 (Polychromatic418967fa.accept_21_16_1_19_1_10717 37 43 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 271
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 271 (accept_3_3 35 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 271 (accept_3_3 32 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 271 (accept_3_3 29 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 271 (accept_3_3 26 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 43 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 271 (accept_3_3 23 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 271 (accept_3_3 20 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 271 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 43 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 271 (accept_3_3 17 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 271 (Polychromatic418967fa.accept_18_16_7_1_1_6332 16 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 271 (accept_3_3 14 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 43 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 271
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 271 (accept_3_3 11 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 271 (Polychromatic418967fa.accept_27_9_16_1_1_11010 9 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 271 (accept_3_3 8 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 271 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 43 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 271 (accept_3_3 5 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 43 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 43 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 271 (accept_3_3 2 43 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 271 (Polychromatic418967fa.accept_16_1_11_15_1_498 1 43 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 271))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 271
  (allA_succ_of_accept 41 42 271 (accept_3_3 41 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 42 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 271 (accept_3_3 38 42 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 271
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 271 (accept_3_3 35 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 271 (accept_3_3 32 42 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 42 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 271 (accept_3_3 29 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 271 (Polychromatic418967fa.accept_13_2_3_11_1_1287 28 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 271 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 42 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 271 (accept_3_3 26 42 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 271
  (Polychromatic418967fa.accept_11_2_9_7_1_124 24 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 271 (accept_3_3 23 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 271 (accept_3_3 20 42 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 42 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 271
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 271 (accept_3_3 17 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 271 (Polychromatic418967fa.accept_13_2_3_11_1_1287 15 42 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 271 (accept_3_3 14 42 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 271 (accept_3_3 11 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 271 (Polychromatic418967fa.accept_13_10_3_11_1_1923 10 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 271 (accept_3_3 8 42 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 42 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 271
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 271 (accept_3_3 5 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  271 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 42 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 42 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 271 (accept_3_3 2 42 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 271)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 271
  (allA_of_3_1 41 41 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 271 (allA_succ_of_accept 39 40 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 271 (accept_3_3 38 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 271 (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 271 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 40 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 271 (accept_3_3 35 40 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 40 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 271 (accept_3_3 32 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 271 (Polychromatic418967fa.accept_14_3_12_5_1_153 31 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 40 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 271 (accept_3_3 29 40 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 271 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 40 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 271 (accept_3_3 26 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 40 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 271 (accept_3_3 23 40 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 40 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 271 (accept_3_3 20 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 271 (Polychromatic418967fa.accept_22_19_18_7_1_16579 19 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 271 (Polychromatic418967fa.accept_19_18_2_5_1_5682 18 40 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 271 (accept_3_3 17 40 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 40 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 271 (accept_3_3 14 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 271 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 40 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 271 (accept_3_3 11 40 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 40 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 271 (accept_3_3 8 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 40 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 271 (accept_3_3 5 40 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 271 (Polychromatic418967fa.accept_16_4_8_15_1_1113 4 40 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 271 (accept_3_3 2 40 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 271 (Polychromatic418967fa.accept_16_1_8_15_1_1945
  1 40 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  271)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 271 (allA_succ_of_accept 38 39 271 (accept_3_3 38 39 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 37
  39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 271 (accept_3_3 35 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 39 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 271 (accept_3_3 32 39 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 39 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 271 (accept_3_3 29 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 271 (accept_3_3 26 39 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 39 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 271 (accept_3_3 23 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 271 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 39 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 271 (accept_3_3 20 39 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 271 (Polychromatic418967fa.accept_16_3_7_15_1_1130 19 39 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 271
  (Polychromatic418967fa.accept_10_8_9_1_1_189 18 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 271 (accept_3_3 17 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 271 (accept_3_3 14 39 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 39 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 271
  (Polychromatic418967fa.accept_10_2_9_1_1_185 12 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 271 (accept_3_3 11 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 39 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 271 (accept_3_3 8 39 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 39 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 271 (accept_3_3 5 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 271 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 39 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 271 (accept_3_3 2 39 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 39 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 271))))))))))))))))))))))))))))))))))))))) (allB_succ 38 271
  (allA_of_3_1 38 38 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 271 (allA_succ_of_accept 36 37 271
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 271 (accept_3_3 35 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 271 (Polychromatic418967fa.accept_16_1_5_15_1_2918 33 37 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 271 (accept_3_3 32 37 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 37 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 271 (accept_3_3 29 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 271 (Polychromatic418967fa.accept_19_9_18_5_1_7101 28 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 271 (Polychromatic418967fa.accept_23_4_14_18_1_15021 27 37 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 271 (accept_3_3 26 37 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 271 (accept_3_3 23 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 271 (Polychromatic418967fa.accept_14_7_9_5_1_529 21 37 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 271 (accept_3_3 20 37 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 37 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 271 (accept_3_3 17 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 271 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 271 (Polychromatic418967fa.accept_24_15_13_7_1_11652 15 37 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 271 (accept_3_3 14 37 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 271 (Polychromatic418967fa.accept_17_13_3_16_1_5599 13 37
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 271
  (Polychromatic418967fa.accept_22_12_15_7_1_16578 12 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 37 271 (accept_3_3 11 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 37 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 271 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 37 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 271 (accept_3_3 8 37 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 271 (Polychromatic418967fa.accept_14_7_9_5_1_529 7
  37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 271 (accept_3_3 5 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 37 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 37 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 271 (accept_3_3 2 37 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 271 (Polychromatic418967fa.accept_16_1_5_15_1_2918 1 37 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 271))))))))))))))))))))))))))))))))))))) (allB_succ 36 271
  (allA_succ_of_accept 35 36 271 (accept_3_3 35 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 271 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 36 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 271 (accept_3_3 32 36 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 271
  (Polychromatic418967fa.accept_13_4_10_11_1_1908 30 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 271 (accept_3_3 29 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 271 (Polychromatic418967fa.accept_13_2_10_11_1_1276 28 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 271 (accept_3_3 26 36 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 271 (accept_3_3 23 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 271 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 271 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 36 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 271 (accept_3_3 20 36 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 36 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 271 (accept_3_3 17 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 271 (Polychromatic418967fa.accept_13_3_10_11_1_1293 16 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 271 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 36 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 271 (accept_3_3 14 36 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 271
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 271 (accept_3_3 11 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 271 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 36 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 271 (accept_3_3 8 36 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 36 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 271 (accept_3_3 5 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 36 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 36 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 271 (accept_3_3 2 36 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 36 271 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 36 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 271)))))))))))))))))))))))))))))))))))) (allB_succ 35 271
  (allA_of_3_1 35 35 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 271 (allA_succ_of_accept 33 34 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 271 (accept_3_3 32 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 34 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 271 (accept_3_3 29 34 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 34 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 271 (accept_3_3 26 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 34 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 271 (accept_3_3 23 34 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 34 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 271 (accept_3_3 20 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 271 (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 34 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 271 (accept_3_3 17 34 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 34 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 271 (accept_3_3 14 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 34 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 271 (accept_3_3 11 34 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 271 (Polychromatic418967fa.accept_13_10_8_11_1_1985 10 34 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 271 (accept_3_3 8 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 34 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 34 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 271 (accept_3_3 5 34 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 34 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 271 (accept_3_3 2 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34
  271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 271)))))))))))))))))))))))))))))))))) (allB_succ 33 271 (allA_succ_of_accept 32 33 271 (accept_3_3 32 33
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 271
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 33 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 33 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 271 (accept_3_3 29 33 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 33 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 271 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 33 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 271 (accept_3_3 26
  33 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 271
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 33 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 33 271 (Polychromatic418967fa.accept_16_8_1_15_1_1982 24 33 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 271 (accept_3_3 23 33 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 33 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 21
  33 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 271 (accept_3_3 20 33
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 271
  (Polychromatic418967fa.accept_15_4_3_1_1_487 19 33 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 33 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 271 (accept_3_3 17 33 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 33 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 271 (Polychromatic418967fa.accept_12_3_9_7_1_472
  15 33 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 271 (accept_3_3 14
  33 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 271
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 33 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 33 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 33 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 271 (accept_3_3 11 33 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 33 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 271 (Polychromatic418967fa.accept_13_9_7_11_1_1292
  9 33 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 271 (accept_3_3 8 33
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 271 (Polychromatic418967fa.accept_9_7_6_1_1_709
  7 33 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 271 (accept_3_3 5 33 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 33 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 271 (accept_3_3 2 33 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 271 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 33 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 271))))))))))))))))))))))))))))))))) (allB_succ 32 271
  (allA_of_3_1 32 32 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 271 (allA_succ_of_accept 30 31 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 271 (accept_3_3 29 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 271 (Polychromatic418967fa.accept_17_11_14_16_1_1270 28 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 271 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 31 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 271 (accept_3_3 26 31 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 31 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 271 (accept_3_3 23 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 31 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 271 (accept_3_3 20 31 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 271 (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 31 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 271
  (Polychromatic418967fa.accept_26_18_5_11_1_16577 18 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 31 271 (accept_3_3 17 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 31 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 31 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 31 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 271 (accept_3_3 14 31 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 271 (Polychromatic418967fa.accept_11_2_9_7_1_124
  13 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 271 (accept_3_3 11 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 271 (Polychromatic418967fa.accept_18_10_13_1_1_7736 10 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 31 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 271 (accept_3_3 8 31 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 271 (accept_3_3 5 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  271 (Polychromatic418967fa.accept_19_4_12_5_1_8615 4 31 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 31 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 271 (accept_3_3 2 31 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 31 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 271))))))))))))))))))))))))))))))) (allB_succ 30 271
  (allA_succ_of_accept 29 30 271 (accept_3_3 29 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 271 (Polychromatic418967fa.accept_13_2_4_11_1_2003 28 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 271 (Polychromatic418967fa.accept_20_7_10_11_1_9577 27 30 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 271 (accept_3_3 26 30 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 271 (accept_3_3 23 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 271 (accept_3_3 20 30 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 271 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 30 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 271 (accept_3_3 17 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 30 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 271 (accept_3_3 14 30 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 271
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 271 (accept_3_3 11 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  30 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 30 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 271 (accept_3_3 8 30 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 30 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 271 (accept_3_3 5 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 30 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 30 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 30 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 271 (accept_3_3 2 30 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 30 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 271)))))))))))))))))))))))))))))) (allB_succ 29 271 (allA_of_3_1
  29 29 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 271 (allA_succ_of_accept 27 28 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 271 (accept_3_3 26 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 271 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 271 (Polychromatic418967fa.accept_16_8_12_15_1_2005 24 28 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 271 (accept_3_3 23 28 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 28 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 271 (accept_3_3 20 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 271 (Polychromatic418967fa.accept_15_3_13_1_1_479 18 28 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 271 (accept_3_3 17 28 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 271 (Polychromatic418967fa.accept_13_3_2_11_1_1999 16 28 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 271 (accept_3_3 14 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 271 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 271 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 28 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 271 (accept_3_3 11 28 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 28 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 271 (accept_3_3 8 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  271 (Polychromatic418967fa.accept_19_7_9_5_1_8590 7 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 28 271 (Polychromatic418967fa.accept_23_6_5_18_1_16576 6 28 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 271 (accept_3_3 5 28 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 271 (Polychromatic418967fa.accept_13_4_2_11_1_733 4 28 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 271 (accept_3_3 2 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28
  271 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 28 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 271)))))))))))))))))))))))))))) (allB_succ 27 271 (allA_succ_of_accept 26 27 271 (accept_3_3 26 27 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25
  27 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 271
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 271 (accept_3_3 23 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 271 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 27 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 271 (accept_3_3 20 27 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 271 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 27 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 271 (accept_3_3 17 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 271 (accept_3_3 14 27 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 271 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 27 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 271
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 271 (accept_3_3 11 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 271 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 27 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 271 (accept_3_3 8 27 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 271 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 27 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 271
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 271 (accept_3_3 5 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 27 271 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 27 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 271 (accept_3_3 2 27 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 27 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 27 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 271))))))))))))))))))))))))))) (allB_succ 26 271 (allA_of_3_1 26
  26 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 271 (allA_succ_of_accept 24 25 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 271 (accept_3_3 23 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 25 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 271 (accept_3_3 20 25 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 25 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 271 (accept_3_3 17 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 25 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 271 (accept_3_3 14 25 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 271 (accept_3_3 11 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 25 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 271 (accept_3_3 8 25 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 271 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 25 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 271 (accept_3_3 5 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  271 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 25 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 271 (accept_3_3 2 25 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 271))))))))))))))))))))))))) (allB_succ 24 271
  (allA_succ_of_accept 23 24 271 (accept_3_3 23 24 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  24 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 24 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 24 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 271 (accept_3_3 20 24 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 271 (Polychromatic418967fa.accept_23_19_1_18_1_16575 19 24 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 271
  (Polychromatic418967fa.accept_21_18_3_19_1_10708 18 24 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 271 (accept_3_3 17 24 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 24 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 24 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 271 (accept_3_3 14 24 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 13
  24 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 24 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 271 (accept_3_3 11 24 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 271 (Polychromatic418967fa.accept_15_10_9_1_1_3688 10 24 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 271 (accept_3_3 8 24 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 271
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 24 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 271 (accept_3_3 5 24 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  271 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 24 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 271 (accept_3_3 2 24 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 271)))))))))))))))))))))))) (allB_succ 23 271 (allA_of_3_1 23 23
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 271 (allA_succ_of_accept 21 22 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 271 (accept_3_3 20 22 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 22 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 22 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 271 (accept_3_3 17 22 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 22 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 271 (accept_3_3 14 22 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 22 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 271 (accept_3_3 11 22 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 22 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 271 (accept_3_3 8 22 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 22 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 22 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 271 (accept_3_3 5 22 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 22 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 271 (accept_3_3 2 22 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 271)))))))))))))))))))))) (allB_succ 21
  271 (allA_succ_of_accept 20 21 271 (accept_3_3 20 21 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 271 (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 21 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 271 (accept_3_3 17 21 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 21 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 271 (accept_3_3 14 21 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 21 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 271 (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 21 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 271 (accept_3_3 11 21 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 271
  (Polychromatic418967fa.accept_13_9_8_11_1_725 9 21 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 271 (accept_3_3 8 21 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 21 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 271 (accept_3_3 5 21 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 271 (Polychromatic418967fa.accept_11_3_10_7_1_129 3
  21 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 271 (accept_3_3 2 21 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 271 (Polychromatic418967fa.accept_13_1_8_11_1_724 1
  21 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 271))))))))))))))))))))) (allB_succ
  20 271 (allA_of_3_1 20 20 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 271 (allA_succ_of_accept 18 19
  271 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 19 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 271 (accept_3_3 17 19 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 271 (Polychromatic418967fa.accept_25_16_19_21_1_9694 16 19 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 271 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 19 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 271 (accept_3_3 14 19 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 271
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 13 19 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 19 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 19 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 271 (accept_3_3 11 19 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 19 271 (Polychromatic418967fa.accept_20_10_19_11_1_2384 10 19 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 271
  (Polychromatic418967fa.accept_25_9_19_21_1_16574 9 19 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 271 (accept_3_3 8 19 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19
  271 (Polychromatic418967fa.accept_16_7_3_15_1_2940 7 19 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 19 271 (Polychromatic418967fa.accept_25_6_19_21_1_16573 6 19 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 271 (accept_3_3 5 19 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 19 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 271
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 19 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 19 271 (accept_3_3 2 19 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19
  271 (Polychromatic418967fa.accept_17_1_2_16_1_5596 1 19 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 19 271))))))))))))))))))) (allB_succ 18 271 (allA_succ_of_accept 17 18 271 (accept_3_3 17 18 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16
  18 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 18 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 18 271 (accept_3_3 14 18 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  18 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 18 271 (Polychromatic418967fa.accept_16_12_2_15_1_490 12 18 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 271 (accept_3_3 11 18 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 271 (Polychromatic418967fa.accept_19_10_18_5_1_5673 10 18
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 18 271 (accept_3_3 8 18 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18
  271 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 18 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 18 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 18 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 271 (accept_3_3 5 18 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 271 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 18 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 271
  (Polychromatic418967fa.accept_10_3_8_1_1_182 3 18 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 271 (accept_3_3 2 18 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18
  271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 271)))))))))))))))))) (allB_succ 17 271 (allA_of_3_1 17 17 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 271 (allA_succ_of_accept 15 16 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 271 (accept_3_3 14 16 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 16 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 16 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 271 (accept_3_3 11 16 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 16 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 271 (accept_3_3 8 16 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 16 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 16 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 271 (accept_3_3 5 16 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 16 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 271 (accept_3_3 2 16 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 271 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 16 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 271)))))))))))))))) (allB_succ 15 271 (allA_succ_of_accept 14 15
  271 (accept_3_3 14 15 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 15 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 15 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 271 (accept_3_3 11 15 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 15 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9
  15 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 271 (accept_3_3 8 15 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7
  15 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 15 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 271 (accept_3_3 5 15 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 271 (accept_3_3 2 15 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 271 (Polychromatic418967fa.accept_17_1_15_16_1_2202 1 15 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 271))))))))))))))) (allB_succ 14 271 (allA_of_3_1 14 14 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 271 (allA_succ_of_accept 12 13 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 13 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 271 (accept_3_3 11 13 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 271 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 13 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 271 (accept_3_3 8 13 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 271 (accept_3_3 5 13 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 13 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 13 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 271 (accept_3_3 2 13 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 271))))))))))))) (allB_succ 12 271 (allA_succ_of_accept 11 12
  271 (accept_3_3 11 12 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 271
  (Polychromatic418967fa.accept_13_10_12_11_1_731 10 12 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 12 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 271 (accept_3_3 8 12 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 6
  12 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 271 (accept_3_3 5 12 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 4
  12 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 271
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 12 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 271 (accept_3_3 2 12 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  271 (Polychromatic418967fa.accept_13_1_12_11_1_728 1 12 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 271)))))))))))) (allB_succ 11 271 (allA_of_3_1 11 11 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 10 271 (allA_succ_of_accept 9 10 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 271 (accept_3_3 8 10 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 271 (Polychromatic418967fa.accept_15_7_10_1_1_1836
  7 10 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 271
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 10 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 271 (accept_3_3 5 10 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  271 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 10 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 10 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 271 (accept_3_3 2 10 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 271)))))))))) (allB_succ 9 271 (allA_succ_of_accept 8
  9 271 (accept_3_3 8 9 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 271
  (Polychromatic418967fa.accept_13_7_9_11_1_705 7 9 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 271 (accept_3_3 5 9 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 9
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 271 (accept_3_3 2 9 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 271 (Polychromatic418967fa.accept_13_1_9_11_1_703 1
  9 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 271))))))))) (allB_succ 8 271
  (allA_of_3_1 8 8 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 271 (allA_succ_of_accept 6 7 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 7 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 271 (accept_3_3 5 7 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 271
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 7 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 271 (accept_3_3 2 7 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 271 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 7 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 271))))))) (allB_succ 6 271 (allA_succ_of_accept 5 6 271
  (accept_3_3 5 6 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 6 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 6 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 271 (accept_3_3 2 6 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 271)))))) (allB_succ 5 271 (allA_of_3_1 5 5 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 271 (allA_succ_of_accept 3 4 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 271 (accept_3_3 2 4 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 4 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 271)))) (allB_succ 3 271 (allA_succ_of_accept 2 3 271 (accept_3_3 2 3 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 3 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 271))) (allB_succ 2 271 (allA_of_3_1 2 2 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


