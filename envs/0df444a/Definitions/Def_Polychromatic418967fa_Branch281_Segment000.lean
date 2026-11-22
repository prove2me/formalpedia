-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch281_Segment000
-- name    : Polychromatic418967fa_Branch281_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:52:16.604165+00:00
-- url     : https://prove2.me/theorems/32d90bb2-c7a2-4951-a501-9ee1d65c9cbc
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

def Polychromatic418967fa.branch_281_segment_000 : allB 123 281 :=
  allB_succ 122 281 (allA_succ_of_accept 121 122 281 (accept_3_2 121 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 122 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 120 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 119 122
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 122 281 (accept_3_2 118 122
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 122 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 117 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 122 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 116 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 122 281 (accept_3_2 115 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 122 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 114 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 122 281
  (Polychromatic418967fa.accept_10_3_2_1_1_839 113 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 122 281 (accept_3_2 112 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 122 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 110 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 122 281 (accept_3_2 109 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 122 281 (Polychromatic418967fa.accept_17_6_3_9_1_7739 108 122
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 122 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 107 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 122 281 (accept_3_2 106 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 122 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 122 281 (Polychromatic418967fa.accept_11_5_1_6_1_774 104 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 122 281 (accept_3_2 103 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 122 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 102 122
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 122 281
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 101 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 122 281 (accept_3_2 100 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 122 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 122 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 122 281 (accept_3_2 97 122 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 122 281 (Polychromatic418967fa.accept_7_5_3_1_1_424
  96 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 122 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 122 281 (accept_3_2 94 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 122 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 122 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 92 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 122 281 (accept_3_2 91 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 122 281 (Polychromatic418967fa.accept_13_12_5_8_1_1101 90 122
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 122 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 89 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 122 281 (accept_3_2 88 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 122 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 86 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 122 281 (accept_3_2 85 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 122 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 122 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 122 281 (accept_3_2 82 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 122 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 122 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 122 281 (accept_3_2 79 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 122 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 122 281
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 77 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 122 281 (accept_3_2 76 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 122 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 122 281 (accept_3_2 73 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 122 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 122 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 122 281 (accept_3_2 70 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 122 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 122 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 122 281 (accept_3_2 67 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 122 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 122 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 122 281 (accept_3_2 64 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 122 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 122 281 (accept_3_2 61 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 122 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 122 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 122 281 (accept_3_2 58 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 122 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 122 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 122 281 (accept_3_2 55 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 122 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 122 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 122 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 122 281 (accept_3_2 52 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 122 281 (Polychromatic418967fa.accept_15_5_2_11_1_1596 50 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 122 281 (accept_3_2 49 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 122 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 122 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 122 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 122 281 (accept_3_2 46 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 122 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 122 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 122 281 (accept_3_2 43 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 122 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 122 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 122 281
  (Polychromatic418967fa.accept_18_5_14_11_1_2073 41 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 122 281 (accept_3_2 40 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 281 (Polychromatic418967fa.accept_11_5_1_6_1_774 38 122
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 122 281 (accept_3_2 37 122
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 122 281
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 281 (accept_3_2 34 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 122 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 281 (accept_3_2 31
  122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 122 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 281 (accept_3_2 28 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 281 (Polychromatic418967fa.accept_7_5_3_1_1_424
  26 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 281 (accept_3_2 25
  122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 281
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 281 (accept_3_2 22 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 122 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 281 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 281 (accept_3_2 19
  122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 122 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 281 (accept_3_2 16 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 281 (Polychromatic418967fa.accept_13_1_5_8_1_207
  14 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 281 (accept_3_2 13
  122 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 281 (accept_3_2 10 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 122 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 281 (accept_3_2 7 122
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 281
  (Polychromatic418967fa.accept_9_6_5_2_1_421 6 122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 122 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 281 (accept_3_2 4 122 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 122 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 2
  122 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 281 (accept_3_2 1 122
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 281 (allA_of_3_0 121 121 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 281
  (allA_succ_of_accept 119 120 281 (Polychromatic418967fa.accept_14_7_8_1_1_1621 119 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 120 281 (accept_3_2 118 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 117 120 281 (Polychromatic418967fa.accept_17_15_1_9_1_10058 117 120 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 116 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 120 281 (accept_3_2 115 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 114 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 120 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 113 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 120 281 (accept_3_2 112 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 281 (Polychromatic418967fa.accept_13_7_3_8_1_1750 111 120
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 120 281
  (Polychromatic418967fa.accept_17_8_1_9_1_7738 110 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 120 281 (accept_3_2 109 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 120 281 (Polychromatic418967fa.accept_16_12_8_9_1_2583 108 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 107 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 281 (accept_3_2 106 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 120
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 120 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 104 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 120 281 (accept_3_2 103 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 120 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 102 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 120 281 (Polychromatic418967fa.accept_21_17_15_8_1_6799 101 120 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 281 (accept_3_2 100 120 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 281
  (Polychromatic418967fa.accept_18_9_12_11_1_5642 99 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 120 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 120 281 (accept_3_2 97 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 120 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 95 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 120 281 (accept_3_2 94 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 120 281 (Polychromatic418967fa.accept_11_5_10_6_1_793 93 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 120 281 (Polychromatic418967fa.accept_16_12_8_9_1_2583 92 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 120 281 (accept_3_2 91 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 120 281 (Polychromatic418967fa.accept_21_6_15_8_1_9895 90 120
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 120 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 89 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 120 281 (accept_3_2 88 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 120 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 86 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 120 281 (accept_3_2 85 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 120 281 (Polychromatic418967fa.accept_16_4_8_9_1_4639 84 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 120 281
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 83 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 120 281 (accept_3_2 82 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 120 281 (Polychromatic418967fa.accept_16_1_8_9_1_3462 81 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 120 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 120 281 (accept_3_2 79 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 120 281 (accept_3_2 76 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 120 281 (Polychromatic418967fa.accept_21_12_15_8_1_5238 75 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 120 281 (Polychromatic418967fa.accept_13_9_3_8_1_573 74 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 120 281 (accept_3_2 73 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 120 281 (Polychromatic418967fa.accept_13_7_3_8_1_1750 72 120
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 120 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 120 281 (accept_3_2 70 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 120 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 120 281 (accept_3_2 67 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 120 281 (Polychromatic418967fa.accept_17_15_1_9_1_10058 66 120 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 120 281
  (Polychromatic418967fa.accept_14_9_8_1_1_2381 65 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 120 281 (accept_3_2 64 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 120 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 120 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 281 (accept_3_2 61 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 120 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 120 281 (accept_3_2 58 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 120 281 (Polychromatic418967fa.accept_13_5_3_8_1_1117 57 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 120 281 (Polychromatic418967fa.accept_21_14_15_8_1_5281 56 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 120 281 (accept_3_2 55 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 120 281 (Polychromatic418967fa.accept_17_3_1_9_1_9012 54 120
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 120 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 120 281 (accept_3_2 52 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 120 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 281 (accept_3_2 49 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 281 (Polychromatic418967fa.accept_13_9_3_8_1_573 48 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 281
  (Polychromatic418967fa.accept_16_15_8_9_1_2563 47 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 120 281 (accept_3_2 46 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 120 281 (Polychromatic418967fa.accept_18_9_12_11_1_5642 45 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 120 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 281 (accept_3_2 43 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 120 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 120 281 (accept_3_2 40 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 120 281 (Polychromatic418967fa.accept_16_7_8_9_1_9427 39 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 120 281 (Polychromatic418967fa.accept_11_5_10_6_1_793 38 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 281 (accept_3_2 37 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 281 (Polychromatic418967fa.accept_16_4_8_9_1_4639 36 120
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 120 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 120 281 (accept_3_2 34 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 120 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 281 (accept_3_2 31 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 281 (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 120 281
  (Polychromatic418967fa.accept_19_10_6_15_1_6444 29 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 120 281 (accept_3_2 28 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 120 281 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 120 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 120 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 281 (accept_3_2 25 120 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431
  24 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 120 281 (accept_3_2 22 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 120 281 (Polychromatic418967fa.accept_14_7_8_1_1_1621 21 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 120 281 (Polychromatic418967fa.accept_13_7_3_8_1_1750 20 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 281 (accept_3_2 19 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 281 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 120
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 281 (accept_3_2 16 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 120 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 281 (accept_3_2 13 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 281 (Polychromatic418967fa.accept_16_12_8_9_1_2583 12 120 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 281
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 281 (accept_3_2 10 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  120 281 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 120 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 281 (accept_3_2 7 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 120 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 120 281 (accept_3_2 4 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  120 281 (Polychromatic418967fa.accept_17_3_1_9_1_9012 3 120 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 120 281 (Polychromatic418967fa.accept_14_2_8_1_1_1647 2 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 281 (accept_3_2 1 120 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 120
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 281 (allA_succ_of_accept 118 119 281 (accept_3_2 118 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 281 (Polychromatic418967fa.accept_15_12_14_11_1_4375 117 119 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 281
  (Polychromatic418967fa.accept_21_11_14_8_1_5256 116 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 119 281 (accept_3_2 115 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 114 119 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 119 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 113 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 281 (accept_3_2 112 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 119 281
  (Polychromatic418967fa.accept_13_7_2_8_1_1746 111 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 110 119 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 119 281 (accept_3_2 109 119 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 119 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 108 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 281
  (Polychromatic418967fa.accept_19_12_5_15_1_13338 107 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 119 281 (accept_3_2 106 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 119 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 105 119 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 281 (Polychromatic418967fa.accept_14_6_7_1_1_78 104 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 281 (accept_3_2 103 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 119 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 119 281 (Polychromatic418967fa.accept_13_10_2_8_1_2603 101 119 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 281 (accept_3_2 100 119 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 281 (Polychromatic418967fa.accept_16_3_7_9_1_3474 99 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 98 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 119 281 (accept_3_2 97 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 119 281 (Polychromatic418967fa.accept_19_1_5_15_1_3722 96 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 119 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 95 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 281 (accept_3_2 94 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 281 (Polychromatic418967fa.accept_15_3_14_11_1_1579 93 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 281
  (Polychromatic418967fa.accept_10_2_9_1_1_185 92 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 281 (accept_3_2 91 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 281 (Polychromatic418967fa.accept_21_5_14_8_1_6818 89 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 281 (accept_3_2 88 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 281 (Polychromatic418967fa.accept_15_12_14_11_1_4375 87
  119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 281 (accept_3_2 85 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 281 (Polychromatic418967fa.accept_13_6_2_8_1_1782 84 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 281 (Polychromatic418967fa.accept_14_13_7_1_1_1618 83 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 281 (accept_3_2 82 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 281 (Polychromatic418967fa.accept_29_23_3_20_1_17251 81
  119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 281
  (Polychromatic418967fa.accept_11_3_9_6_1_105 80 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 281 (accept_3_2 79 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 119 281 (Polychromatic418967fa.accept_16_13_7_9_1_2606 77 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 281 (accept_3_2 76 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 75 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 281 (accept_3_2 73 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 281 (Polychromatic418967fa.accept_13_6_2_8_1_1782 71 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 281 (accept_3_2 70 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 69 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 281
  (Polychromatic418967fa.accept_10_8_9_1_1_189 68 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 281 (accept_3_2 67 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 65 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 281 (accept_3_2 64 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 281 (Polychromatic418967fa.accept_15_3_14_11_1_1579 63 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 281 (accept_3_2 61 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 281 (Polychromatic418967fa.accept_26_8_15_21_1_17250 60 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 281 (Polychromatic418967fa.accept_13_7_2_8_1_1746 59 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 281 (accept_3_2 58 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 281 (Polychromatic418967fa.accept_15_12_14_11_1_4375 57
  119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 281
  (Polychromatic418967fa.accept_16_8_7_9_1_7052 56 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 281 (accept_3_2 55 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 281 (Polychromatic418967fa.accept_21_11_14_8_1_5256 53 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 281 (accept_3_2 52 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 281 (Polychromatic418967fa.accept_16_3_7_9_1_3474 51 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 281 (accept_3_2 49 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 47 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 281 (accept_3_2 46 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 281
  (Polychromatic418967fa.accept_19_6_5_15_1_13340 44 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 119 281 (accept_3_2 43 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 119 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 281 (Polychromatic418967fa.accept_14_13_7_1_1_1618 41 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 281 (accept_3_2 40 119
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 281
  (Polychromatic418967fa.accept_19_1_5_15_1_3722 39 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 119 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 281 (accept_3_2 37 119 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 119 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 281
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 281 (accept_3_2 34 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 281 (Polychromatic418967fa.accept_13_7_2_8_1_1746 33 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 281 (accept_3_2 31 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 119 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 281
  (Polychromatic418967fa.accept_16_13_7_9_1_2606 29 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 281 (accept_3_2 28 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 281 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 281 (accept_3_2 25 119 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 281 (Polychromatic418967fa.accept_16_8_7_9_1_7052 24 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 281
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 23 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 281 (accept_3_2 22 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 281 (Polychromatic418967fa.accept_25_21_19_6_1_11997 21 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 281 (Polychromatic418967fa.accept_13_7_2_8_1_1746 20 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 281 (accept_3_2 19 119 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 281
  (Polychromatic418967fa.accept_19_17_5_15_1_7921 17 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 119 281 (accept_3_2 16 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 119 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 119 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 281 (accept_3_2 13 119 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 281 (Polychromatic418967fa.accept_10_2_9_1_1_185
  12 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 281
  (Polychromatic418967fa.accept_19_11_5_15_1_2436 11 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 119 281 (accept_3_2 10 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 119 281 (Polychromatic418967fa.accept_19_9_5_15_1_2544 9 119 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 119 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 281 (accept_3_2 7 119 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 281
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 281 (accept_3_2 4 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 119 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 281 (accept_3_2 1 119 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 281 (allA_of_3_0 118 118 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 281
  (allA_succ_of_accept 116 117 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 117 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 281 (accept_3_2 115 117 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 117 281 (Polychromatic418967fa.accept_10_4_7_1_1_471 114 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 281
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 113 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 117 281 (accept_3_2 112 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 117 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 111 117 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 117
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 281 (accept_3_2 109 117
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 108 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 117 281 (Polychromatic418967fa.accept_16_11_5_9_1_1617 107 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 117 281 (accept_3_2 106 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 117 281 (Polychromatic418967fa.accept_18_15_9_11_1_4371 105 117 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 104 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 117 281 (accept_3_2 103 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 117 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 102 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 117 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 281 (accept_3_2 100 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 117 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 99 117
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 98 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 117 281 (accept_3_2 97 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 117 281 (Polychromatic418967fa.accept_10_6_7_1_1_1297 96 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 117 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 281 (accept_3_2 94 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 281 (Polychromatic418967fa.accept_16_13_5_9_1_4682 93 117 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 281 (accept_3_2 91 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 117 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 90 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 281 (Polychromatic418967fa.accept_11_1_7_6_1_378 89 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 281 (accept_3_2 88 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 117 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 117 281 (accept_3_2 85 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 117 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 117 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 281 (accept_3_2 82 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 281 (accept_3_2 79 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 117 281 (Polychromatic418967fa.accept_11_1_7_6_1_378 78 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 117 281 (Polychromatic418967fa.accept_16_13_5_9_1_4682 77 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 281 (accept_3_2 76 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 117
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 281 (accept_3_2 73 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 117 281 (Polychromatic418967fa.accept_21_9_12_8_1_5255 72 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 117 281 (Polychromatic418967fa.accept_20_11_17_1_1_13117 71 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 281 (accept_3_2 70 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 117 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 281 (accept_3_2 67 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 117 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 117 281 (Polychromatic418967fa.accept_16_1_5_9_1_1649 65 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 281 (accept_3_2 64 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 117
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 281 (accept_3_2 61 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 117 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 117 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 281 (accept_3_2 58 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 281 (Polychromatic418967fa.accept_17_6_15_9_1_1791 57 117 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 281 (accept_3_2 55 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 117 281 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 117 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 281 (accept_3_2 52 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 281 (accept_3_2 49 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 117 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 281 (Polychromatic418967fa.accept_19_9_3_15_1_2429 47 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 281 (accept_3_2 46 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 117 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 281 (accept_3_2 43 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 117 281 (Polychromatic418967fa.accept_27_15_9_11_1_17249 42 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 281 (accept_3_2 40 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 117 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 281 (accept_3_2 37 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 281 (Polychromatic418967fa.accept_17_1_15_9_1_1743 35 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 281 (accept_3_2 34 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 281 (Polychromatic418967fa.accept_16_1_5_9_1_1649 33 117
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 281 (accept_3_2 31 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 281 (Polychromatic418967fa.accept_16_14_5_9_1_5901 30 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 281 (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 281 (accept_3_2 28 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 117 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 281 (accept_3_2 25 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 281 (Polychromatic418967fa.accept_11_1_7_6_1_378 23 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 281 (accept_3_2 22 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 281 (Polychromatic418967fa.accept_22_21_7_17_1_17248 21
  117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 281 (accept_3_2 19 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 281 (accept_3_2 16 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 281 (accept_3_2 13 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 281 (accept_3_2 10 117 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 281 (Polychromatic418967fa.accept_19_9_3_15_1_2429 9 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 281 (accept_3_2 7 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 281 (Polychromatic418967fa.accept_21_5_12_8_1_6807 5 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 281 (accept_3_2 4 117 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 117 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 281 (accept_3_2 1 117 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 281 (allA_succ_of_accept 115 116 281 (accept_3_2 115 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 116 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 114 116 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 116 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 113 116
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 116 281 (accept_3_2 112 116
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 116 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 116 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 110 116 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 116 281 (accept_3_2 109 116 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 116 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 108 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 116 281
  (Polychromatic418967fa.accept_10_7_6_1_1_486 107 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 116 281 (accept_3_2 106 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 116 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 104 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 281 (accept_3_2 103 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 116 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 102 116
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 116 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 101 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 116 281 (accept_3_2 100 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 116 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 98 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 116 281 (accept_3_2 97 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 116 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 96 116 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 116 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 95 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 116 281 (accept_3_2 94 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 116 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 92 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 116 281 (accept_3_2 91 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 116 281 (Polychromatic418967fa.accept_17_5_14_9_1_5104 90 116
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 116 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 89 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 116 281 (accept_3_2 88 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 116 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 86 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 116 281 (accept_3_2 85 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 116 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 116 281
  (Polychromatic418967fa.accept_13_5_12_8_1_198 83 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 116 281 (accept_3_2 82 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 116 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 116 281 (accept_3_2 79 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 116 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 77 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 116 281 (accept_3_2 76 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 116 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 74 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 116 281 (accept_3_2 73 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 116 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 116
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 281
  (Polychromatic418967fa.accept_20_11_16_1_1_13090 71 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 116 281 (accept_3_2 70 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 116 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 116 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 116 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 281 (accept_3_2 67 116 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 66
  116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 281
  (Polychromatic418967fa.accept_10_5_6_1_1_836 65 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 281 (accept_3_2 64 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 281 (accept_3_2 61 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 116 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 281 (accept_3_2 58 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 281 (Polychromatic418967fa.accept_13_4_12_8_1_197 56 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 281 (accept_3_2 55 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 116 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 281 (accept_3_2 52 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 281 (accept_3_2 49 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 281 (accept_3_2 46 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 281 (Polychromatic418967fa.accept_13_5_12_8_1_198 44 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 281 (accept_3_2 43 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 116 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 281 (accept_3_2 40 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 281 (accept_3_2 37 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 281 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 116 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 281
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 281 (accept_3_2 34 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 281 (accept_3_2 31 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 281 (accept_3_2 28 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 281 (accept_3_2 25 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 281 (accept_3_2 22 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 281 (Polychromatic418967fa.accept_13_7_12_8_1_199 20 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 281 (accept_3_2 19 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 281 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 116
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 281 (accept_3_2 16 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 281 (accept_3_2 13 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 281
  (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 281 (accept_3_2 10 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 281 (Polychromatic418967fa.accept_16_8_4_9_1_4666 8 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 281 (accept_3_2 7 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 116 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 281 (accept_3_2 4 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 281 (accept_3_2 1 116 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 281 (allA_of_3_0 115 115 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 281
  (allA_succ_of_accept 113 114 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 113 114 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 114 281 (accept_3_2 112 114 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 114 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 281
  (Polychromatic418967fa.accept_15_5_9_11_1_4398 110 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 114 281 (accept_3_2 109 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 114 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 108 114 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 107 114
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 281 (accept_3_2 106 114
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 281
  (Polychromatic418967fa.accept_10_5_4_1_1_842 105 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 114 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 104 114 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 114 281 (accept_3_2 103 114 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 114 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 101 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 114 281 (accept_3_2 100 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 114 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 114 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 98 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 114 281 (accept_3_2 97 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 114 281 (Polychromatic418967fa.accept_13_5_10_8_1_1127 96 114 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 114 281 (accept_3_2 94 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 114 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 114 281 (Polychromatic418967fa.accept_14_8_2_1_1_1652 92 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 114 281 (accept_3_2 91 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 114 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 114 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 114 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 89 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 114 281 (accept_3_2 88 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 114 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 114 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 114 281 (accept_3_2 85 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 114 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 114 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 114 281 (accept_3_2 82 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 114 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 81 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 114 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 80 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 281 (accept_3_2 79 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 114 281 (Polychromatic418967fa.accept_14_8_2_1_1_1652 78 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 114 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 114 281 (accept_3_2 76 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 114 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 114 281 (Polychromatic418967fa.accept_25_24_14_6_1_12016 74 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 281 (accept_3_2 73 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 114 281 (Polychromatic418967fa.accept_13_7_10_8_1_567 72 114
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 114 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 114 281 (accept_3_2 70 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 114 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 114 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 281 (accept_3_2 67 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 114 281
  (Polychromatic418967fa.accept_10_5_4_1_1_842 65 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 114 281 (accept_3_2 64 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 114 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 114 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 281 (accept_3_2 61 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 281 (Polychromatic418967fa.accept_16_12_2_9_1_3461 60 114 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 114 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 114 281 (accept_3_2 58 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 114 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 114 281 (Polychromatic418967fa.accept_13_4_10_8_1_1817 56 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 281 (accept_3_2 55 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 281 (Polychromatic418967fa.accept_13_2_10_8_1_1126 54 114
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 114 281 (accept_3_2 52 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 114 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 114 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 281 (accept_3_2 49 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 114 281 (accept_3_2 46 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 114 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 114 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 281 (accept_3_2 43 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 281 (Polychromatic418967fa.accept_22_20_4_17_1_15821 42 114 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 114 281 (accept_3_2 40 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 114 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 114 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 281 (accept_3_2 37 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 281 (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 281 (accept_3_2 34 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 114 281 (Polychromatic418967fa.accept_13_7_10_8_1_567 33 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 114 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 281 (accept_3_2 31 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 281
  (Polychromatic418967fa.accept_23_6_22_5_1_10974 29 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 114 281 (accept_3_2 28 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 114 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 114 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 281 (accept_3_2 25 114 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 281 (Polychromatic418967fa.accept_7_3_2_1_1_225
  24 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 281 (accept_3_2 22 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 114 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 114 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 281 (accept_3_2 19 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 281 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 114 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 281 (accept_3_2 16 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 114 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 114 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 281 (accept_3_2 13 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 281 (accept_3_2 10 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  114 281 (Polychromatic418967fa.accept_22_9_4_17_1_17247 9 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 114 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 281 (accept_3_2 7 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 114 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 281 (accept_3_2 4 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  114 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 114 281 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 281 (accept_3_2 1 114 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 114
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 281 (allA_succ_of_accept 112 113 281 (accept_3_2 112 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 111 113 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 281 (Polychromatic418967fa.accept_15_5_8_11_1_2350 110
  113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 281 (accept_3_2 109
  113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 281
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 108 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 107 113 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 281 (accept_3_2 106 113 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 105 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 281
  (Polychromatic418967fa.accept_16_8_1_9_1_847 104 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 281 (accept_3_2 103 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 281 (Polychromatic418967fa.accept_16_5_1_9_1_4621 101 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 281 (accept_3_2 100 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 281 (Polychromatic418967fa.accept_19_4_18_15_1_7899 99 113
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 98 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 281 (accept_3_2 97 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 96 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 281 (Polychromatic418967fa.accept_13_4_9_8_1_1736 95 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 281 (accept_3_2 94 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 93 113 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 281
  (Polychromatic418967fa.accept_10_2_3_1_1_481 92 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 281 (accept_3_2 91 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 281 (Polychromatic418967fa.accept_13_12_9_8_1_2595 90 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 113 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 281 (accept_3_2 88 113 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 87 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 281
  (Polychromatic418967fa.accept_11_9_3_6_1_797 86 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 281 (accept_3_2 85 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 281 (Polychromatic418967fa.accept_19_7_18_15_1_5061 83 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 281 (accept_3_2 82 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 281 (Polychromatic418967fa.accept_13_3_9_8_1_4202 81 113
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 80 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 281 (accept_3_2 79 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 281 (Polychromatic418967fa.accept_13_12_9_8_1_2595 77 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 281 (accept_3_2 76 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 113 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 281
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 74 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 281 (accept_3_2 73 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 281 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 113 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 281 (accept_3_2 70 113 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 281
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 68 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 281 (accept_3_2 67 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 281 (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 281 (accept_3_2 64 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 281 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 113
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 281 (accept_3_2 61 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 281 (Polychromatic418967fa.accept_13_7_9_8_1_188 59 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 281 (accept_3_2 58 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 113 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 281
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 56 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 281 (accept_3_2 55 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 281 (Polychromatic418967fa.accept_17_3_11_9_1_5100 54 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 113 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 281 (accept_3_2 52 113 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 281
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 50 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 281 (accept_3_2 49 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 281 (Polychromatic418967fa.accept_19_9_18_15_1_3715 47 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 281 (accept_3_2 46 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 281 (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 113
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 281 (accept_3_2 43 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 281 (Polychromatic418967fa.accept_11_8_3_6_1_1855 41 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 281 (accept_3_2 40 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 113 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 281
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 38 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 281 (accept_3_2 37 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 281 (Polychromatic418967fa.accept_17_2_11_9_1_1739 36 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 113 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 281 (accept_3_2 34 113 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 281
  (Polychromatic418967fa.accept_10_2_3_1_1_481 32 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 281 (accept_3_2 31 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 281 (Polychromatic418967fa.accept_13_3_9_8_1_4202 29 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 281 (accept_3_2 28 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 281 (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 113
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 281 (accept_3_2 25 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 281 (Polychromatic418967fa.accept_19_4_18_15_1_7899 23 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 281 (accept_3_2 22 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 113 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 281
  (Polychromatic418967fa.accept_11_9_3_6_1_797 20 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 281 (accept_3_2 19 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 281 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 113 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 281 (accept_3_2 16 113 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 281
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 14 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 281 (accept_3_2 13 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 281 (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 281 (accept_3_2 10 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 281 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 113 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 281 (accept_3_2 7 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 281 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 281 (accept_3_2 4 113 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 113 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 281
  (Polychromatic418967fa.accept_10_2_3_1_1_481 2 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 281 (accept_3_2 1 113 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 281 (allA_of_3_0 112 112 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 281
  (allA_succ_of_accept 110 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 110 111 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 281 (accept_3_2 109 111 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 281 (Polychromatic418967fa.accept_15_3_6_11_1_855 108 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 107 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 281 (accept_3_2 106 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 281 (accept_3_2 103 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 111 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 281
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 101 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 111 281 (accept_3_2 100 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 111 281 (Polychromatic418967fa.accept_15_9_6_11_1_1586 99 111 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 111 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 281 (accept_3_2 97 111 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 281 (Polychromatic418967fa.accept_7_5_6_1_1_407
  96 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 95 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 281 (accept_3_2 94 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 281 (accept_3_2 91 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 89 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 281 (accept_3_2 88 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 281 (accept_3_2 85 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 281 (Polychromatic418967fa.accept_11_7_1_6_1_1281 84 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 281
  (Polychromatic418967fa.accept_23_14_19_5_1_17246 83 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 111 281 (accept_3_2 82 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 111 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 111 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 111 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 281 (accept_3_2 79 111 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 78
  111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 281 (accept_3_2 76 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 281 (accept_3_2 73 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 281 (accept_3_2 70 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 281 (accept_3_2 67 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 281 (accept_3_2 64 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 281 (Polychromatic418967fa.accept_14_7_13_1_1_922 63 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 281 (accept_3_2 61 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 281 (accept_3_2 58 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 281 (accept_3_2 55 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 281 (accept_3_2 52 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 281 (accept_3_2 49 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 281 (Polychromatic418967fa.accept_13_9_7_8_1_1122 48 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 281 (accept_3_2 46 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 281 (accept_3_2 43 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 281 (accept_3_2 40 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 281 (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 281 (accept_3_2 37 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 281 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 111 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 281 (accept_3_2 34 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 281 (accept_3_2 31 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 281
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 281 (accept_3_2 28 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 281 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 281 (accept_3_2 25 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 281 (accept_3_2 22 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 281 (accept_3_2 19 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 281 (accept_3_2 16 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 281 (accept_3_2 13 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 111 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 281
  (Polychromatic418967fa.accept_19_11_16_15_1_11951 11 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 111 281 (accept_3_2 10 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 111 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 111 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 281 (accept_3_2 7 111 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 281 (accept_3_2 4 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 281 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 111 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 281 (accept_3_2 1 111 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 281 (allA_succ_of_accept 109 110 281 (accept_3_2 109 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 108 110 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 107 110
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 110 281 (accept_3_2 106 110
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 110 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 105 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 110 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 104 110 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 110 281 (accept_3_2 103 110 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 110 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 102 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 110 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 101 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 110 281 (accept_3_2 100 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 110 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 110 281 (Polychromatic418967fa.accept_15_8_5_11_1_2358 98 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 110 281 (accept_3_2 97 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 110 281 (Polychromatic418967fa.accept_15_6_5_11_1_2378 96 110
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 110 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 110 281 (accept_3_2 94 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 110 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 110 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 92 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 281 (accept_3_2 91 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 110 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 90 110 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 110 281
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 89 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 110 281 (accept_3_2 88 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 110 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 110 281 (Polychromatic418967fa.accept_17_1_8_9_1_1810 86 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 110 281 (accept_3_2 85 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 110 281 (Polychromatic418967fa.accept_15_9_5_11_1_5416 84 110
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 110 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 110 281 (accept_3_2 82 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 110 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 110 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 80 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 110 281 (accept_3_2 79 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 110 281 (Polychromatic418967fa.accept_21_15_5_8_1_17228 78 110 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 281
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 77 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 110 281 (accept_3_2 76 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 110 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 110 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 281 (accept_3_2 73 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 281 (Polychromatic418967fa.accept_26_20_6_21_1_17245 72 110 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 110 281 (accept_3_2 70 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 110 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 110 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 68 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 281 (accept_3_2 67 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 110 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 110 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 110 281
  (Polychromatic418967fa.accept_20_5_10_1_1_11750 65 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 110 281 (accept_3_2 64 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 110 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 110 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 62 110 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 281 (accept_3_2 61 110 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 110 281 (Polychromatic418967fa.accept_7_4_5_1_1_418
  60 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 110 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 281 (accept_3_2 58 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 56 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 110 281 (accept_3_2 55 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 110 281 (Polychromatic418967fa.accept_13_2_6_8_1_1092 54 110
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 110 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 110 281 (accept_3_2 52 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 110 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 110 281 (Polychromatic418967fa.accept_13_11_6_8_1_1121 50 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 110 281 (accept_3_2 49 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 110 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 281 (accept_3_2 46 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 110 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 110 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 44 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 281 (accept_3_2 43 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 281 (Polychromatic418967fa.accept_25_17_10_6_1_17244 42
  110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 110 281 (accept_3_2 40 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 110 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 110 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 281 (accept_3_2 37 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 281 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 110 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 110 281 (accept_3_2 34 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 110 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 110 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 281 (accept_3_2 31 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 281 (Polychromatic418967fa.accept_23_7_18_5_1_12556 30 110 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 110 281
  (Polychromatic418967fa.accept_20_9_10_1_1_192 29 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 110 281 (accept_3_2 28 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 110 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 110 281 (Polychromatic418967fa.accept_27_26_2_11_1_17243 26 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 281 (accept_3_2 25 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 110 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 281 (accept_3_2 22 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 110 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 281 (accept_3_2 19 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 281 (accept_3_2 16 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 281 (Polychromatic418967fa.accept_13_1_6_8_1_208 14 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 281 (accept_3_2 13 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 281 (Polychromatic418967fa.accept_21_12_5_8_1_9929 12 110
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 110 281 (accept_3_2 10 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  110 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 110 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 281 (accept_3_2 7 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 110 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 281
  (Polychromatic418967fa.accept_16_5_14_9_1_2572 5 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 281 (accept_3_2 4 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 281 (Polychromatic418967fa.accept_13_2_6_8_1_1092 2 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 281 (accept_3_2 1 110 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 281 (allA_of_3_0 109 109 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 281
  (allA_succ_of_accept 107 108 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 107 108 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 281 (accept_3_2 106 108 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 108 281 (Polychromatic418967fa.accept_17_3_6_9_1_2761 105 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 281
  (Polychromatic418967fa.accept_15_14_3_11_1_850 104 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 108 281 (accept_3_2 103 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 108 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 102 108 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 101 108
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 281 (accept_3_2 100 108
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 281
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 99 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 108 281 (Polychromatic418967fa.accept_15_8_3_11_1_849 98 108 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 108 281 (accept_3_2 97 108 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 108 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 108 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 95
  108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 281 (accept_3_2 94
  108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 108 281 (Polychromatic418967fa.accept_19_16_13_15_1_16011 92 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 108 281 (accept_3_2 91 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 108 281 (Polychromatic418967fa.accept_13_12_4_8_1_1120 90 108 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 108 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 89 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 108 281 (accept_3_2 88 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 108 281 (Polychromatic418967fa.accept_13_9_4_8_1_1752 87 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 108 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 86 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 108 281 (accept_3_2 85 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 108 281 (Polychromatic418967fa.accept_16_4_12_9_1_2567 84 108 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 281
  (Polychromatic418967fa.accept_10_3_8_1_1_182 83 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 108 281 (accept_3_2 82 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 108 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 108 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 80 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 108 281 (accept_3_2 79 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 108 281 (Polychromatic418967fa.accept_19_2_13_15_1_9274 78 108
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 77 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 108 281 (accept_3_2 76 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 108 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 108 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 281 (accept_3_2 73 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 108 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 281
  (Polychromatic418967fa.accept_17_3_6_9_1_2761 71 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 108 281 (accept_3_2 70 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 108 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 108 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 281 (accept_3_2 67 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 108 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 66 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 108 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 108 281 (accept_3_2 64 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 108 281 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 108 281 (Polychromatic418967fa.accept_13_10_4_8_1_2570 62 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 281 (accept_3_2 61 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 108 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 108 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 108 281
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 108 281 (accept_3_2 58 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 108 281 (Polychromatic418967fa.accept_21_15_3_8_1_6822 57 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 108 281 (Polychromatic418967fa.accept_16_8_12_9_1_2569 56 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 281 (accept_3_2 55 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 108 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 108 281 (accept_3_2 52 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 108 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 108 281 (Polychromatic418967fa.accept_13_11_4_8_1_1098 50 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 281 (accept_3_2 49 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 281 (Polychromatic418967fa.accept_13_9_4_8_1_1752 48 108
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 108 281 (accept_3_2 46 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 108 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 108 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 281 (accept_3_2 43 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 281 (Polychromatic418967fa.accept_17_8_6_9_1_7768 42 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 281
  (Polychromatic418967fa.accept_22_19_20_17_1_12678 41 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 108 281 (accept_3_2 40 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 108 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 108 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 281 (Polychromatic418967fa.accept_13_12_4_8_1_1120 38 108
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 281 (accept_3_2 37 108
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 281
  (Polychromatic418967fa.accept_11_3_9_6_1_105 36 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 108 281 (Polychromatic418967fa.accept_13_9_4_8_1_1752 35 108 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 281 (accept_3_2 34 108 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 108 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 281 (accept_3_2 31
  108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 108 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 108 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 281 (accept_3_2 28 108 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 108 281 (Polychromatic418967fa.accept_20_7_8_1_1_5856 27 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 108 281 (accept_3_2 25 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 108 281 (Polychromatic418967fa.accept_13_11_4_8_1_1098 24 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 108 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 281 (accept_3_2 22 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 281
  (Polychromatic418967fa.accept_16_4_12_9_1_2567 20 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 281 (accept_3_2 19 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 108 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 108 281 (Polychromatic418967fa.accept_19_17_13_15_1_1402 17 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 281 (accept_3_2 16 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 281 (Polychromatic418967fa.accept_17_15_6_9_1_13743 15 108
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 281
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 281 (accept_3_2 13 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 108 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 108 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 281 (accept_3_2 10 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 281
  (Polychromatic418967fa.accept_15_8_3_11_1_849 8 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 281 (accept_3_2 7 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  108 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 108 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 281 (accept_3_2 4 108 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 281 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 108 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 281 (accept_3_2 1 108 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 281 (allA_succ_of_accept 106 107 281 (accept_3_2 106 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 105 107 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 104 107
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 281 (accept_3_2 103 107
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 107 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 281 (accept_3_2 100 107 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 281 (Polychromatic418967fa.accept_15_9_2_11_1_2391 99 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 98 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 281 (accept_3_2 97 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 281 (accept_3_2 94 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 93 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 281
  (Polychromatic418967fa.accept_14_8_9_1_1_3313 92 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 281 (accept_3_2 91 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 89 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 281 (accept_3_2 88 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 107 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 281 (accept_3_2 85 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 281 (accept_3_2 82 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 281 (Polychromatic418967fa.accept_15_6_2_11_1_325 81 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 281 (accept_3_2 79 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 281 (accept_3_2 76 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 281 (accept_3_2 73 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 281 (Polychromatic418967fa.accept_13_7_3_8_1_1750 72 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 281 (Polychromatic418967fa.accept_20_11_7_1_1_8874 71 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 281 (accept_3_2 70 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 107 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 281 (accept_3_2 67 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 281 (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 281 (accept_3_2 64 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 107
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 281 (accept_3_2 61 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 281 (accept_3_2 58 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 281
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 281 (accept_3_2 55 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 281 (Polychromatic418967fa.accept_16_5_11_9_1_861 53 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 281 (accept_3_2 52 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 107 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 281 (accept_3_2 49 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 281 (Polychromatic418967fa.accept_11_3_8_6_1_788 47 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 281 (accept_3_2 46 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 107 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 281
  (Polychromatic418967fa.accept_10_4_7_1_1_471 44 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 281 (accept_3_2 43 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 281 (accept_3_2 40 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 281 (accept_3_2 37 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 281 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 281 (Polychromatic418967fa.accept_13_9_3_8_1_573 35 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 281 (accept_3_2 34 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 107 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 281 (accept_3_2 31 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 281 (Polychromatic418967fa.accept_17_12_5_9_1_6372 29 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 281 (accept_3_2 28 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 107 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 281 (accept_3_2 25 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 281 (accept_3_2 22 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 281 (accept_3_2 19 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 281 (accept_3_2 16 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 281 (accept_3_2 13 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 281 (accept_3_2 10 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 281 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 107 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 281
  (Polychromatic418967fa.accept_14_8_9_1_1_3313 8 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 281 (accept_3_2 7 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 281 (accept_3_2 4 107 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 107 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 281 (accept_3_2 1 107 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 281 (allA_of_3_0 106 106 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 281
  (allA_succ_of_accept 104 105 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 105 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 281 (accept_3_2 103 105 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 281
  (Polychromatic418967fa.accept_19_6_10_15_1_10659 101 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 105 281 (accept_3_2 100 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 99 105 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 105 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 281 (accept_3_2 97 105 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 281 (Polychromatic418967fa.accept_10_6_5_1_1_482
  96 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 95 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 281 (accept_3_2 94 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 281 (accept_3_2 91 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 281 (Polychromatic418967fa.accept_13_12_1_8_1_1779 90 105 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 89 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 281 (accept_3_2 88 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 87 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 281 (accept_3_2 85 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 281
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 83 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 281 (accept_3_2 82 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 281 (Polychromatic418967fa.accept_18_9_15_11_1_5693 81 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 281 (accept_3_2 79 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 281 (Polychromatic418967fa.accept_14_8_7_1_1_1615 78 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 281 (accept_3_2 76 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 281 (accept_3_2 73 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 281 (Polychromatic418967fa.accept_13_7_1_8_1_1778 72 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 281 (accept_3_2 70 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 281 (accept_3_2 67 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 281
  (Polychromatic418967fa.accept_25_15_5_6_1_13797 65 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 105 281 (accept_3_2 64 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 105 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 105 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 105 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 281 (accept_3_2 61 105 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 281
  (Polychromatic418967fa.accept_18_6_15_11_1_3141 60 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 105 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 281 (accept_3_2 58 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 105 281 (accept_3_2 55 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 105 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 105 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 281 (accept_3_2 52 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 281 (accept_3_2 49 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 105 281 (Polychromatic418967fa.accept_19_9_10_15_1_11957 47 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 281 (accept_3_2 46 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 281 (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 105
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 281 (accept_3_2 43 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 105 281 (Polychromatic418967fa.accept_18_6_15_11_1_3141 42 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 105 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 281 (accept_3_2 40 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 281 (accept_3_2 37 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 281 (accept_3_2 34 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 281 (Polychromatic418967fa.accept_13_7_1_8_1_1778 33 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 281 (accept_3_2 31 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 281 (accept_3_2 28 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 105
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 281 (accept_3_2 25 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 281 (accept_3_2 22 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 281 (accept_3_2 19 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 281 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 281 (accept_3_2 16 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 281 (accept_3_2 13 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 281 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 281 (accept_3_2 10 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 281 (accept_3_2 7 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 281 (accept_3_2 4 105 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 281 (accept_3_2 1 105 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 281 (allA_succ_of_accept 103 104 281 (accept_3_2 103 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 281 (Polychromatic418967fa.accept_19_6_9_15_1_3694 101
  104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 281 (accept_3_2 100
  104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 99 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 281 (accept_3_2 97 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 281 (Polychromatic418967fa.accept_10_5_4_1_1_842
  95 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 104 281 (accept_3_2 94
  104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 104 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 93 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 104 281 (Polychromatic418967fa.accept_16_12_8_9_1_2583 92 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 281 (accept_3_2 91 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 104 281 (Polychromatic418967fa.accept_20_10_4_1_1_8840 90 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 89 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 104 281 (accept_3_2 88 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 104 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 86 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 281 (accept_3_2 85 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 104 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 281
  (Polychromatic418967fa.accept_20_3_4_1_1_11728 83 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 281 (accept_3_2 82 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 281 (accept_3_2 79 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 104 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 281
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 77 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 104 281 (accept_3_2 76 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 104 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 74 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 281 (accept_3_2 73 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 104 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 281 (accept_3_2 70 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 281 (accept_3_2 67 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 281 (accept_3_2 64 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 281 (accept_3_2 61 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 281
  (Polychromatic418967fa.accept_18_5_14_11_1_2073 59 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 104 281 (accept_3_2 58 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 281 (Polychromatic418967fa.accept_11_1_5_6_1_397 56 104
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 281 (accept_3_2 55 104
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 104 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 281 (accept_3_2 52 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 281 (Polychromatic418967fa.accept_12_2_8_5_1_408
  50 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 281 (accept_3_2 49
  104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 281
  (Polychromatic418967fa.accept_9_3_5_2_1_28 48 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 104 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 281 (accept_3_2 46 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 44
  104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 281 (accept_3_2 43
  104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 281
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 104 281 (Polychromatic418967fa.accept_17_7_2_9_1_6396 41 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 281 (accept_3_2 40 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 104 281 (Polychromatic418967fa.accept_12_2_8_5_1_408
  38 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 281 (accept_3_2 37
  104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 281
  (Polychromatic418967fa.accept_16_4_8_9_1_4639 36 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 104 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 281 (accept_3_2 34 104 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 281
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 32 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 104 281 (accept_3_2 31 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 104 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 104 281 (Polychromatic418967fa.accept_19_10_9_15_1_11965 29 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 281 (accept_3_2 28 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 281 (accept_3_2 25 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 281 (accept_3_2 22 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 281
  (Polychromatic418967fa.accept_16_4_8_9_1_4639 20 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 281 (accept_3_2 19 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 281 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 281 (accept_3_2 16 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 281 (accept_3_2 13 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 281 (Polychromatic418967fa.accept_17_11_2_9_1_6358 11 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 281 (accept_3_2 10 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 281 (accept_3_2 7 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 281 (accept_3_2 4 104 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 281 (accept_3_2 1 104 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 281 (allA_of_3_0 103 103 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 281 (allA_succ_of_accept 101
  102 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 102 281 (accept_3_2 100 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 102 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 102 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 102 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 281 (accept_3_2 97 102 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 281 (Polychromatic418967fa.accept_7_5_4_1_1_412
  96 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 102 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 102 281 (accept_3_2 94 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 102 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 93 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 102 281 (Polychromatic418967fa.accept_13_1_11_8_1_2562 92 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 281 (accept_3_2 91 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 281 (Polychromatic418967fa.accept_19_14_7_15_1_3732 90 102
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 102 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 89 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 102 281 (accept_3_2 88 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 102 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 102 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 86 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 281 (accept_3_2 85 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 281 (Polychromatic418967fa.accept_13_6_11_8_1_1111 84 102 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 102 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 102 281 (accept_3_2 82 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 102 281 (Polychromatic418967fa.accept_13_3_11_8_1_1094 81 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 102 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 281 (accept_3_2 79 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 102 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 102 281 (accept_3_2 76 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 102 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 102 281 (Polychromatic418967fa.accept_11_8_3_6_1_1855 74 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 281 (accept_3_2 73 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 281 (Polychromatic418967fa.accept_21_9_18_8_1_11475 72 102
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 102 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 102 281 (accept_3_2 70 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 102 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 102 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 281 (accept_3_2 67 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 102 281
  (Polychromatic418967fa.accept_19_8_7_15_1_13364 65 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 102 281 (accept_3_2 64 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 102 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 102 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 281 (accept_3_2 61 102 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 281 (Polychromatic418967fa.accept_9_6_3_2_1_431
  60 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 102 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 102 281 (accept_3_2 58 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 102 281 (Polychromatic418967fa.accept_21_15_18_8_1_6809 57 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 102 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 281 (accept_3_2 55 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 102 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 102 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 102 281 (accept_3_2 52 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 102 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 102 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 281 (accept_3_2 49 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 281 (Polychromatic418967fa.accept_13_9_11_8_1_195 48 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 102 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 102 281 (accept_3_2 46 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 102 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 102 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 281 (accept_3_2 43 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 102 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 281 (accept_3_2 40 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 102 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 102 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 281 (accept_3_2 37 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 281 (accept_3_2 34 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 102 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 102 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 281 (accept_3_2 31 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 281 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 281
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 281 (accept_3_2 28 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 102 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 102 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 281 (accept_3_2 25 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 281 (accept_3_2 22 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 102 281 (Polychromatic418967fa.accept_23_21_10_5_1_17242 21 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 281 (Polychromatic418967fa.accept_11_9_3_6_1_797 20 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 281 (accept_3_2 19 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 281 (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 102
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 281 (accept_3_2 16 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 102 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 102 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 281 (accept_3_2 13 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 281 (accept_3_2 10 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 281 (accept_3_2 7 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 102 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 281 (accept_3_2 4 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 281 (Polychromatic418967fa.accept_16_2_6_9_1_3473 2 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 281 (accept_3_2 1 102 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 281 (allA_succ_of_accept 100 101 281 (accept_3_2 100 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 281 (Polychromatic418967fa.accept_19_4_6_15_1_7916 99 101 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 281 (Polychromatic418967fa.accept_13_7_10_8_1_567 98 101
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 281 (accept_3_2 97 101
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 96 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 101 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 281 (accept_3_2 94 101 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 101 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 281 (Polychromatic418967fa.accept_8_4_5_1_1_299
  92 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 281 (accept_3_2 91
  101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 281
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 90 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 101 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 281 (accept_3_2 88 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 281 (Polychromatic418967fa.accept_19_11_6_15_1_14622 87 101 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 86 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 281 (accept_3_2 85 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 281 (Polychromatic418967fa.accept_13_5_10_8_1_1127 83 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 281 (accept_3_2 82 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 101 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 281
  (Polychromatic418967fa.accept_13_2_10_8_1_1126 80 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 281 (accept_3_2 79 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 281 (Polychromatic418967fa.accept_16_14_5_9_1_5901 78 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 281 (Polychromatic418967fa.accept_13_12_10_8_1_3343 77 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 281 (accept_3_2 76 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 101 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 281 (accept_3_2 73 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 281 (Polychromatic418967fa.accept_24_23_5_17_1_12309 71 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 281 (accept_3_2 70 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 281 (Polychromatic418967fa.accept_13_4_10_8_1_1817 69 101
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 68 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 281 (accept_3_2 67 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 281 (Polychromatic418967fa.accept_19_9_6_15_1_9256 66 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 281 (accept_3_2 64 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 281 (Polychromatic418967fa.accept_13_11_10_8_1_1804 63 101 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 281
  (Polychromatic418967fa.accept_16_14_5_9_1_5901 62 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 281 (accept_3_2 61 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 281 (Polychromatic418967fa.accept_11_4_2_6_1_389 59 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 281 (accept_3_2 58 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 281 (Polychromatic418967fa.accept_13_5_10_8_1_1127 57 101
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 281
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 56 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 281 (accept_3_2 55 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 281 (accept_3_2 52 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 281
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 50 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 101 281 (accept_3_2 49 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 101 281 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 101 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 101 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 281 (accept_3_2 46 101 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 281
  (Polychromatic418967fa.accept_16_13_5_9_1_4682 45 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 101 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 101 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 281 (accept_3_2 43 101 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 101 281 (Polychromatic418967fa.accept_17_8_16_9_1_8952 42 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 281
  (Polychromatic418967fa.accept_13_2_10_8_1_1126 41 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 281 (accept_3_2 40 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 281 (Polychromatic418967fa.accept_13_12_10_8_1_3343 38 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 281 (accept_3_2 37 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 101 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 281
  (Polychromatic418967fa.accept_19_16_6_15_1_2441 35 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 101 281 (accept_3_2 34 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 101 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 101 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 101 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 281 (accept_3_2 31 101 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 30
  101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 281
  (Polychromatic418967fa.accept_16_13_5_9_1_4682 29 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 281 (accept_3_2 28 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 281 (Polychromatic418967fa.accept_16_11_5_9_1_1617 27 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 281 (accept_3_2 25 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 281 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 101 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 281 (accept_3_2 22 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 281 (Polychromatic418967fa.accept_19_2_6_15_1_16015 21 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 281 (accept_3_2 19 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 281
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 281 (accept_3_2 16 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 281 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 281 (Polychromatic418967fa.accept_16_14_5_9_1_5901 14 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 281 (accept_3_2 13 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 101 281 (accept_3_2 10 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  101 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 101 281 (Polychromatic418967fa.accept_17_8_16_9_1_8952 8 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 281 (accept_3_2 7 101 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 281 (Polychromatic418967fa.accept_17_6_16_9_1_5129 6 101
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 281 (accept_3_2 4 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 281 (Polychromatic418967fa.accept_21_3_17_8_1_8402 3 101 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 281 (accept_3_2 1 101 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 281 (allA_of_3_0 100 100 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 281 (allA_succ_of_accept 98 99
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 281 (accept_3_2 97 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96
  99 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 96 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 99 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 95 99 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 281 (accept_3_2 94 99 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 93 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 281 (accept_3_2 91 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 281 (Polychromatic418967fa.accept_17_4_14_9_1_5105 89 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 281 (accept_3_2 88 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 281 (Polychromatic418967fa.accept_16_7_3_9_1_2557 87 99 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 281 (accept_3_2 85 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 281 (Polychromatic418967fa.accept_18_12_9_11_1_4370 84 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 281 (Polychromatic418967fa.accept_24_11_3_17_1_17241 83 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 281 (accept_3_2 82 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 99 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 281 (accept_3_2 79 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 281 (Polychromatic418967fa.accept_15_2_9_11_1_1551 77 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 281 (accept_3_2 76 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 75 99 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 281 (accept_3_2 73 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 281 (Polychromatic418967fa.accept_16_7_3_9_1_2557 71 99 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 281 (accept_3_2 70 99 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 69 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 281 (accept_3_2 67 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 65 99 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 281 (accept_3_2 64 99 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 281 (Polychromatic418967fa.accept_17_12_14_9_1_5079 63 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 281 (accept_3_2 61 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 281 (Polychromatic418967fa.accept_16_12_3_9_1_5886 60 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 281 (Polychromatic418967fa.accept_21_17_15_8_1_6799 59 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 281 (accept_3_2 58 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 99 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 281 (accept_3_2 55 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 281 (Polychromatic418967fa.accept_22_9_11_17_1_17240 53 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 281 (accept_3_2 52 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 51 99 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 281 (accept_3_2 49 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 281 (Polychromatic418967fa.accept_15_2_9_11_1_1551 47 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 281 (accept_3_2 46 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 99 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 281 (accept_3_2 43 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 281 (Polychromatic418967fa.accept_23_18_7_5_1_7475 41 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 281 (accept_3_2 40 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 281 (Polychromatic418967fa.accept_16_7_3_9_1_2557 39 99 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 281 (accept_3_2 37 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 99 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 281 (accept_3_2 34 99 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 281 (accept_3_2 31 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 281 (Polychromatic418967fa.accept_17_12_14_9_1_5079 29 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 281 (accept_3_2 28 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 281 (Polychromatic418967fa.accept_19_8_4_15_1_1414 27 99
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 281 (accept_3_2 25 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 281 (Polychromatic418967fa.accept_19_5_4_15_1_2512 24 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 281 (Polychromatic418967fa.accept_16_7_3_9_1_2557 23 99 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 281 (accept_3_2 22 99 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 281 (accept_3_2 19 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 281 (Polychromatic418967fa.accept_15_2_9_11_1_1551 17 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 281 (accept_3_2 16 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 99 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 281 (accept_3_2 13 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 281 (Polychromatic418967fa.accept_19_11_4_15_1_5052 11 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 281 (accept_3_2 10 99 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 99 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 281 (accept_3_2 7 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 99 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 281 (accept_3_2 4 99 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 281 (Polychromatic418967fa.accept_21_3_15_8_1_12962 3 99 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 281 (accept_3_2 1 99 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  281 (allA_succ_of_accept 97 98 281 (accept_3_2 97 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 281 (accept_3_2 94 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 92 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 281 (accept_3_2 91 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 281 (Polychromatic418967fa.accept_13_12_7_8_1_1104 90 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331 89 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 281 (accept_3_2 88 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 86 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 281 (accept_3_2 85 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 281 (accept_3_2 82 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 281 (accept_3_2 79 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 281 (accept_3_2 76 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 281
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 74 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 281 (accept_3_2 73 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 281 (Polychromatic418967fa.accept_15_12_8_11_1_4383 72 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 281 (accept_3_2 70 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 281 (accept_3_2 67 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 281 (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 281 (accept_3_2 64 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 281
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 62 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 281 (accept_3_2 61 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 281 (accept_3_2 58 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 281 (accept_3_2 55 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 281 (Polychromatic418967fa.accept_13_2_7_8_1_4221 54 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 281 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 281 (accept_3_2 52 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 281 (accept_3_2 49 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 281 (accept_3_2 46 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 281 (accept_3_2 43 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 281 (accept_3_2 40 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 281
  (Polychromatic418967fa.accept_11_5_10_6_1_793 38 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 281 (accept_3_2 37 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 281 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 281 (accept_3_2 34 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 281 (accept_3_2 31 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 281 (accept_3_2 28 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 281
  (Polychromatic418967fa.accept_19_7_3_15_1_2428 26 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 281 (accept_3_2 25 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 281 (accept_3_2 22 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 281 (accept_3_2 19 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 281 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 281 (Polychromatic418967fa.accept_16_1_2_9_1_1607 17 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 281 (accept_3_2 16 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 281 (accept_3_2 13 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 281 (accept_3_2 10 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 281 (accept_3_2 7 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 98 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 281 (accept_3_2 4 98 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 281 (Polychromatic418967fa.accept_13_2_7_8_1_4221 2
  98 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 281 (accept_3_2 1 98 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  281 (allA_of_3_0 97 97 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 281 (allA_succ_of_accept 95 96 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 95 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 96 281 (accept_3_2 94 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  96 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 96 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 92 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 281 (accept_3_2 91 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 90 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 96 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 89 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 281 (accept_3_2 88 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  96 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 96 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 281 (accept_3_2 85 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 96 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 83 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 281 (accept_3_2 82 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  96 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 96 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 80 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 281 (accept_3_2 79 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 281 (Polychromatic418967fa.accept_15_3_6_11_1_855 78 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 96 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 281 (accept_3_2 76 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  96 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 96 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 281 (accept_3_2 73 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 96 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 281 (accept_3_2 70 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  96 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 96 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 281 (accept_3_2 67 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 281
  (Polychromatic418967fa.accept_10_5_6_1_1_836 65 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 281 (accept_3_2 64 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  96 281 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 96 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 62 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 281 (accept_3_2 61 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 281 (accept_3_2 58 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  96 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 96 281 (Polychromatic418967fa.accept_21_14_12_8_1_6833 56 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 281 (accept_3_2 55 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 281 (Polychromatic418967fa.accept_15_9_6_11_1_1586 54 96
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 96 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 281 (accept_3_2 52 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  96 281 (Polychromatic418967fa.accept_13_12_5_8_1_1101 51 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 96 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 281 (accept_3_2 49 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 96 281
  (Polychromatic418967fa.accept_10_7_6_1_1_486 47 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 281 (accept_3_2 46 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  96 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 96 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 281 (accept_3_2 43 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 281 (accept_3_2 40 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  96 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 96 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 281 (accept_3_2 37 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 281 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 281 (accept_3_2 34 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 281 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 281 (accept_3_2 31 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 281
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 29 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 281 (accept_3_2 28 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 281 (accept_3_2 25 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 281 (accept_3_2 22 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 281 (accept_3_2 19 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 281 (accept_3_2 16 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 281 (accept_3_2 13 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 281 (accept_3_2 10 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 281 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 281 (accept_3_2 7 96 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 96 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 281 (accept_3_2 4 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 96 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 281 (accept_3_2 1 96 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 281
  (allA_succ_of_accept 94 95 281 (accept_3_2 94 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 93 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 281 (Polychromatic418967fa.accept_15_2_5_11_1_1563 92 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 281 (accept_3_2 91 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 95 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 89 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 281 (accept_3_2 88 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 281 (accept_3_2 85 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 281
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 83 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 281 (accept_3_2 82 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 281 (Polychromatic418967fa.accept_15_6_5_11_1_2378 81 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 281 (accept_3_2 79 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 281
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 77 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 281 (accept_3_2 76 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 281 (accept_3_2 73 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 281 (Polychromatic418967fa.accept_16_8_15_9_1_4676 72 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 281 (accept_3_2 70 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 281 (accept_3_2 67 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 281
  (Polychromatic418967fa.accept_20_5_15_1_1_7278 65 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 281 (accept_3_2 64 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 281 (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 281 (accept_3_2 61 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 281 (accept_3_2 58 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 281 (accept_3_2 55 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 281 (accept_3_2 52 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 281 (accept_3_2 49 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 281 (accept_3_2 46 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 281 (accept_3_2 43 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 281
  (Polychromatic418967fa.accept_21_20_11_8_1_9906 41 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 281 (accept_3_2 40 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 281 (accept_3_2 37 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 281 (accept_3_2 34 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 281 (Polychromatic418967fa.accept_14_4_11_1_1_940 32 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 281 (accept_3_2 31 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 281
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 281 (accept_3_2 28 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 281 (Polychromatic418967fa.accept_20_7_15_1_1_13089 27 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 281 (accept_3_2 25 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 281
  (Polychromatic418967fa.accept_11_1_7_6_1_378 23 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 281 (accept_3_2 22 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 281 (Polychromatic418967fa.accept_17_3_10_9_1_8970 20 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 281 (accept_3_2 19 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 281 (accept_3_2 16 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 281 (accept_3_2 13 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 281
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 281 (accept_3_2 10 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 281 (accept_3_2 7 95 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 281 (accept_3_2 4 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  281 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 95 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 281 (accept_3_2 1 95 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 281
  (allA_of_3_0 94 94 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 281 (allA_succ_of_accept 92 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 281 (accept_3_2 91 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 281 (accept_3_2 88 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 281 (accept_3_2 85 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 281 (accept_3_2 82 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 81 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 281 (accept_3_2 79 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 281 (accept_3_2 76 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 281 (accept_3_2 73 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 281 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 281 (accept_3_2 70 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 281 (accept_3_2 67 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 281 (Polychromatic418967fa.accept_11_10_5_6_1_1842 65 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 281 (accept_3_2 64 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 93 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 281 (accept_3_2 61 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 281 (accept_3_2 58 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 281 (Polychromatic418967fa.accept_17_6_8_9_1_1771 57 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 281 (accept_3_2 55 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 281 (Polychromatic418967fa.accept_11_10_5_6_1_1842 54 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 281 (accept_3_2 52 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 281 (accept_3_2 49 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 281 (Polychromatic418967fa.accept_22_3_5_17_1_9702 47 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 281 (accept_3_2 46 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 93 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 281 (accept_3_2 43 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 281 (accept_3_2 40 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 281 (accept_3_2 37 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 281 (accept_3_2 34 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 281 (accept_3_2 31 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 281 (Polychromatic418967fa.accept_20_10_13_1_1_15956 30 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 281 (Polychromatic418967fa.accept_15_14_3_11_1_850 29 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 281 (accept_3_2 28 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 93 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 281 (accept_3_2 25 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 281 (accept_3_2 22 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 281 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 281 (accept_3_2 19 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 281 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 281 (accept_3_2 16 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 281 (accept_3_2 13 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 281 (Polychromatic418967fa.accept_17_11_8_9_1_8919 11 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 281 (accept_3_2 10 93 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 281 (Polychromatic418967fa.accept_23_9_1_5_1_17239 9 93 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 281 (accept_3_2 7 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 93 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 93 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 281 (accept_3_2 4 93 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 93 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 281 (accept_3_2 1 93 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 281
  (allA_succ_of_accept 91 92 281 (accept_3_2 91 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 281 (Polychromatic418967fa.accept_11_2_4_6_1_2412 90 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 89 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 281 (accept_3_2 88 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 281
  (Polychromatic418967fa.accept_10_6_2_1_1_494 86 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 281 (accept_3_2 85 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 281 (Polychromatic418967fa.accept_13_6_1_8_1_1116 84 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 83 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 281 (accept_3_2 82 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 281
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 80 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 281 (accept_3_2 79 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 281 (Polychromatic418967fa.accept_28_22_8_1_1_17238 78 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 77 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 281 (accept_3_2 76 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 74 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 281 (accept_3_2 73 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 281 (Polychromatic418967fa.accept_13_7_1_8_1_1778 72 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 281 (Polychromatic418967fa.accept_13_6_1_8_1_1116 71 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 281 (accept_3_2 70 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 281
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 68 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 281 (accept_3_2 67 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 66 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 281 (Polychromatic418967fa.accept_14_9_8_1_1_2381 65 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 281 (accept_3_2 64 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 281 (accept_3_2 61 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 281 (Polychromatic418967fa.accept_19_3_16_15_1_9281 60 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 59 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 281 (accept_3_2 58 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 281
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 281 (accept_3_2 55 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 281 (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 281 (accept_3_2 52 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 281 (accept_3_2 49 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 281 (Polychromatic418967fa.accept_13_9_1_8_1_1742 48 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 281 (Polychromatic418967fa.accept_30_17_2_11_1_17237 47 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 281 (accept_3_2 46 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 281
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 44 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 281 (accept_3_2 43 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 281 (Polychromatic418967fa.accept_22_20_4_17_1_15821 42 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 281 (Polychromatic418967fa.accept_19_3_16_15_1_9281 41 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 281 (accept_3_2 40 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 281 (accept_3_2 37 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 281 (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 281 (accept_3_2 34 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 281
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 32 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 281 (accept_3_2 31 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 281 (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 281 (accept_3_2 28 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 281
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 281 (accept_3_2 25 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 281 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 281 (accept_3_2 22 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 281
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 20 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 281 (accept_3_2 19 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 281 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 281 (Polychromatic418967fa.accept_18_17_2_11_1_9749 17 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 281 (accept_3_2 16 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 281 (accept_3_2 13 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 281 (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 281 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 281 (accept_3_2 10 92 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 281
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 8 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 281 (accept_3_2 7 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  281 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 92 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 281 (accept_3_2 4 92 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 281 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2
  92 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 281 (accept_3_2 1 92 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 281
  (allA_of_3_0 91 91 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 281 (allA_succ_of_accept 89 90 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 89 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 90 281 (accept_3_2 88 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  90 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 90 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 86 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 281 (accept_3_2 85 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 281 (Polychromatic418967fa.accept_20_4_10_1_1_13131 84 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 90 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 90 281 (accept_3_2 82 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  90 281 (Polychromatic418967fa.accept_11_4_2_6_1_389 81 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 90 281 (Polychromatic418967fa.accept_17_12_5_9_1_6372 80 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 281 (accept_3_2 79 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 281 (Polychromatic418967fa.accept_21_15_6_8_1_9888 78 90
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 281
  (Polychromatic418967fa.accept_14_7_6_1_1_1656 77 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 281 (accept_3_2 76 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  90 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 90 281 (Polychromatic418967fa.accept_13_9_12_8_1_570 74 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 281 (accept_3_2 73 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 281 (accept_3_2 70 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  90 281 (Polychromatic418967fa.accept_13_4_12_8_1_197 69 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 90 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 281 (accept_3_2 67 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 281 (Polychromatic418967fa.accept_13_1_12_8_1_1818 66 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 90 281 (accept_3_2 64 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  90 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 90 281 (Polychromatic418967fa.accept_13_10_12_8_1_2550 62 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 281 (accept_3_2 61 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 281 (Polychromatic418967fa.accept_24_12_18_17_1_12249 60 90
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 281 (accept_3_2 58 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  90 281 (Polychromatic418967fa.accept_13_5_12_8_1_198 57 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 90 281 (Polychromatic418967fa.accept_13_4_12_8_1_197 56 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 281 (accept_3_2 55 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 281
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 53 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 281 (accept_3_2 52 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  90 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 90 281 (Polychromatic418967fa.accept_22_6_2_17_1_4655 50 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 281 (accept_3_2 49 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 281 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 90 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 281 (accept_3_2 46 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  90 281 (Polychromatic418967fa.accept_19_7_14_15_1_2477 45 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 90 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 281 (accept_3_2 43 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 281 (Polychromatic418967fa.accept_19_4_14_15_1_9231 42 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 281
  (Polychromatic418967fa.accept_17_7_5_9_1_7763 41 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 281 (accept_3_2 40 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  90 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 90 281 (Polychromatic418967fa.accept_25_13_15_6_1_6608 38 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 281 (accept_3_2 37 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 281 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 90
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 90 281 (accept_3_2 34 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  90 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 90 281 (Polychromatic418967fa.accept_19_13_14_15_1_7924 32 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 281 (accept_3_2 31 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 90 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 281
  (Polychromatic418967fa.accept_17_12_5_9_1_6372 29 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 281 (accept_3_2 28 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  90 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 90 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 281 (accept_3_2 25 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 281 (Polychromatic418967fa.accept_17_7_5_9_1_7763 24 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 281 (accept_3_2 22 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 281 (Polychromatic418967fa.accept_14_7_6_1_1_1656 21 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 281 (Polychromatic418967fa.accept_13_7_12_8_1_199 20 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 281 (accept_3_2 19 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 281 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 281
  (Polychromatic418967fa.accept_13_4_12_8_1_197 17 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 281 (accept_3_2 16 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 281 (Polychromatic418967fa.accept_13_1_12_8_1_1818 14 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 281 (accept_3_2 13 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 90 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 281 (accept_3_2 10 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 90 281 (Polychromatic418967fa.accept_27_8_9_11_1_11663 8 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 281 (accept_3_2 7 90 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 281 (Polychromatic418967fa.accept_22_6_2_17_1_4655 6 90 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 281 (accept_3_2 4 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90
  281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 90 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 281 (accept_3_2 1 90 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 90 281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 89 281 (allA_succ_of_accept 88 89 281 (accept_3_2 88 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 89 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 86 89 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 281 (accept_3_2 85 89 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 84
  89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 83 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 281 (accept_3_2 82 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 80 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 281 (accept_3_2 79 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 77 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 281 (accept_3_2 76 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 281 (accept_3_2 73 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 281
  (Polychromatic418967fa.accept_11_5_1_6_1_774 71 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 281 (accept_3_2 70 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 281 (accept_3_2 67 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 281
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 281 (accept_3_2 64 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 281 (Polychromatic418967fa.accept_15_3_14_11_1_1579 63 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 62 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 281 (accept_3_2 61 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 281 (accept_3_2 58 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 281 (Polychromatic418967fa.accept_13_4_11_8_1_1768 56 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 281 (accept_3_2 55 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 281 (Polychromatic418967fa.accept_19_16_13_15_1_16011 54 89
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 281 (accept_3_2 52 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 281 (accept_3_2 49 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 281
  (Polychromatic418967fa.accept_17_13_4_9_1_6390 47 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 281 (accept_3_2 46 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 281 (Polychromatic418967fa.accept_19_6_13_15_1_2406 44 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 281 (accept_3_2 43 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 89 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 281 (accept_3_2 40 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 281 (accept_3_2 37 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 281 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 281
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 281 (accept_3_2 34 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 281 (accept_3_2 31 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 281
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 281 (accept_3_2 28 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 281 (Polychromatic418967fa.accept_19_7_13_15_1_2407 26 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 281 (accept_3_2 25 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 89 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 281 (accept_3_2 22 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 281 (accept_3_2 19 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 281 (accept_3_2 16 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 281 (accept_3_2 13 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 281 (accept_3_2 10 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 281 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 281 (accept_3_2 7 89 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 89 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 281 (accept_3_2 4 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 89 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 89 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 281 (accept_3_2 1 89 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 281 (allA_of_3_0 88 88 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 281
  (allA_succ_of_accept 86 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 281 (accept_3_2 85 87 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 281
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 83 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 281 (accept_3_2 82 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  87 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 87 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 281 (accept_3_2 79 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 87 281 (accept_3_2 76 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  87 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 281 (accept_3_2 73 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 87 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 87 281 (accept_3_2 70 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  87 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 69 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 87 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 281 (accept_3_2 67 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 281 (accept_3_2 64 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  87 281 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 281 (accept_3_2 61 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 87 281 (accept_3_2 58 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  87 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 87 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 281 (accept_3_2 55 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 281 (accept_3_2 52 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  87 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 281 (accept_3_2 49 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 281 (accept_3_2 46 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  87 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 87 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 281 (accept_3_2 43 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 281 (accept_3_2 40 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 281 (accept_3_2 37 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 281 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 281 (accept_3_2 34 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 281 (accept_3_2 31 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 281
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 29 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 281 (accept_3_2 28 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 281 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 281 (accept_3_2 25 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 281 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 281 (accept_3_2 22 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 281 (accept_3_2 19 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 281 (accept_3_2 16 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 281 (Polychromatic418967fa.accept_20_15_7_1_1_5885 15 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 281 (accept_3_2 13 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 281 (accept_3_2 10 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 281 (accept_3_2 7 87 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 281 (accept_3_2 4 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  281 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 281 (accept_3_2 1 87 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 86 281 (allA_succ_of_accept 85 86 281 (accept_3_2 85 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 86 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 86 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 281 (accept_3_2 82 86 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 81
  86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 281 (accept_3_2 79 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 281 (Polychromatic418967fa.accept_10_7_6_1_1_486 77 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 281 (accept_3_2 76 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 281
  (Polychromatic418967fa.accept_18_2_14_11_1_3139 74 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 281 (accept_3_2 73 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 281 (accept_3_2 70 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 281 (accept_3_2 67 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 65 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 281 (accept_3_2 64 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 281 (accept_3_2 61 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 281 (accept_3_2 58 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 281 (accept_3_2 55 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 281 (Polychromatic418967fa.accept_17_3_1_9_1_9012 54 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 281 (accept_3_2 52 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 281
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 50 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 281 (accept_3_2 49 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 281 (accept_3_2 46 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 281 (accept_3_2 43 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 281 (accept_3_2 40 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 281 (accept_3_2 37 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 281 (accept_3_2 34 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 281
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 281 (accept_3_2 31 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 281 (Polychromatic418967fa.accept_16_13_6_9_1_2561 29 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 281 (accept_3_2 28 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 281 (accept_3_2 25 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 281 (accept_3_2 22 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 281 (accept_3_2 19 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 281 (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 281 (accept_3_2 16 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 281
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 281 (accept_3_2 13 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 281 (accept_3_2 10 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 281 (accept_3_2 7 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 86 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 281 (accept_3_2 4 86 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  86 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 281 (accept_3_2 1 86 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 281
  (allA_of_3_0 85 85 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 281 (allA_succ_of_accept 83 84 281
  (Polychromatic418967fa.accept_19_7_8_15_1_2448 83 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 281 (accept_3_2 82 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 81 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 281 (accept_3_2 79 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 77 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 281 (accept_3_2 76 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 281 (Polychromatic418967fa.accept_10_5_4_1_1_842 75 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 281 (Polychromatic418967fa.accept_17_6_16_9_1_5129 74 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 281 (accept_3_2 73 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 281 (Polychromatic418967fa.accept_16_8_4_9_1_4666 72 84 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 281 (accept_3_2 70 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 281 (accept_3_2 67 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 281 (Polychromatic418967fa.accept_13_1_6_8_1_208 66 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 281
  (Polychromatic418967fa.accept_10_5_4_1_1_842 65 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 281 (accept_3_2 64 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 281 (Polychromatic418967fa.accept_13_11_6_8_1_1121 63 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 281 (accept_3_2 61 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 281 (accept_3_2 58 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 281 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 281 (Polychromatic418967fa.accept_11_1_7_6_1_378 56 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 281 (accept_3_2 55 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 281 (Polychromatic418967fa.accept_13_2_6_8_1_1092 54 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 281 (accept_3_2 52 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 281 (accept_3_2 49 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 281 (Polychromatic418967fa.accept_22_4_18_17_1_17236 48 84 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 281
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 281 (accept_3_2 46 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 281 (accept_3_2 43 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 281 (accept_3_2 40 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 281 (Polychromatic418967fa.accept_19_1_8_15_1_3786 39 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 281 (Polychromatic418967fa.accept_22_16_18_17_1_15767 38 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 281 (accept_3_2 37 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 84 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 281 (accept_3_2 34 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 281 (accept_3_2 31 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 281 (Polychromatic418967fa.accept_16_14_4_9_1_1646 30 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 281 (accept_3_2 28 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 281 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 281 (accept_3_2 25 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 281 (accept_3_2 22 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 281 (Polychromatic418967fa.accept_15_5_9_11_1_4398 20 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 281 (accept_3_2 19 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 281 (Polychromatic418967fa.accept_24_18_12_17_1_10620 18 84
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 281 (accept_3_2 16 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 281 (accept_3_2 13 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 281 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 281
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 281 (accept_3_2 10 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 281 (Polychromatic418967fa.accept_18_9_12_11_1_5642 9 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 281 (accept_3_2 7 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 84 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 281 (accept_3_2 4 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  281 (Polychromatic418967fa.accept_19_3_8_15_1_2523 3 84 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 84 281 (Polychromatic418967fa.accept_13_2_6_8_1_1092 2 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 281 (accept_3_2 1 84 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 281
  (allA_succ_of_accept 82 83 281 (accept_3_2 82 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 281 (Polychromatic418967fa.accept_13_3_5_8_1_1099 81 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 281 (Polychromatic418967fa.accept_15_5_8_11_1_2350 80 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 281 (accept_3_2 79 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 281
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 77 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 281 (accept_3_2 76 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 281 (accept_3_2 73 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 281
  (Polychromatic418967fa.accept_16_7_3_9_1_2557 71 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 281 (accept_3_2 70 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 281 (Polychromatic418967fa.accept_17_1_15_9_1_1743 69 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 281 (accept_3_2 67 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 281 (accept_3_2 64 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 281 (Polychromatic418967fa.accept_14_7_13_1_1_922 63 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 281 (accept_3_2 61 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 281 (Polychromatic418967fa.accept_16_12_3_9_1_5886 60 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 281
  (Polychromatic418967fa.accept_21_17_20_8_1_9938 59 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 281 (accept_3_2 58 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 281 (Polychromatic418967fa.accept_15_12_8_11_1_4383 57 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 281 (Polychromatic418967fa.accept_19_18_7_15_1_3733 56 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 281 (accept_3_2 55 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 281
  (Polychromatic418967fa.accept_13_1_5_8_1_207 53 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 281 (accept_3_2 52 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 281 (accept_3_2 49 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 281 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 281 (accept_3_2 46 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 281 (Polychromatic418967fa.accept_20_5_3_1_1_10415 45 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 281 (accept_3_2 43 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 281
  (Polychromatic418967fa.accept_17_7_15_9_1_9019 41 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 281 (accept_3_2 40 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 281 (Polychromatic418967fa.accept_16_7_3_9_1_2557 39 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 281 (accept_3_2 37 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 281 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 281
  (Polychromatic418967fa.accept_14_7_13_1_1_922 35 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 281 (accept_3_2 34 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 281 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 281 (accept_3_2 31 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 281
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 29 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 281 (accept_3_2 28 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 281 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 281 (accept_3_2 25 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 281 (Polychromatic418967fa.accept_17_7_15_9_1_9019 24 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 281 (accept_3_2 22 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 281 (Polychromatic418967fa.accept_14_7_13_1_1_922 21 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 281 (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 281 (accept_3_2 19 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 281
  (Polychromatic418967fa.accept_19_17_7_15_1_6418 17 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 281 (accept_3_2 16 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 281 (Polychromatic418967fa.accept_23_15_14_5_1_17235 15 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 281 (accept_3_2 13 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 83 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 281
  (Polychromatic418967fa.accept_19_11_7_15_1_14688 11 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 83 281 (accept_3_2 10 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 83 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 83 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 281 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 83 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 281 (accept_3_2 7 83 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 281 (accept_3_2 4 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  281 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 83 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 281 (accept_3_2 1 83 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 281 (allA_of_3_0
  82 82 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 281 (allA_succ_of_accept 80 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 81 281 (accept_3_2 79 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  81 281 (Polychromatic418967fa.accept_15_3_6_11_1_855 78 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 81 281 (Polychromatic418967fa.accept_15_2_6_11_1_1587 77 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 281 (accept_3_2 76 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 81 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 281 (accept_3_2 73 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  81 281 (Polychromatic418967fa.accept_13_7_3_8_1_1750 72 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 81 281 (Polychromatic418967fa.accept_28_15_25_1_1_17234 71 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 281 (accept_3_2 70 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 281 (Polychromatic418967fa.accept_15_9_6_11_1_1586 69 81
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 281 (accept_3_2 67 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  81 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 81 281 (Polychromatic418967fa.accept_15_5_6_11_1_854 65 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 281 (accept_3_2 64 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 81 281 (accept_3_2 61 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  81 281 (Polychromatic418967fa.accept_14_4_11_1_1_940 60 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 81 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 281 (accept_3_2 58 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 281 (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 281 (accept_3_2 55 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 281 (Polychromatic418967fa.accept_16_5_1_9_1_4621 53 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 281 (accept_3_2 52 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 281 (accept_3_2 49 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 281 (Polychromatic418967fa.accept_13_9_3_8_1_573 48 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 281 (accept_3_2 46 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 281 (accept_3_2 43 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 281 (Polychromatic418967fa.accept_16_10_1_9_1_4622 42 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 281 (Polychromatic418967fa.accept_23_18_12_5_1_17233 41 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 281 (accept_3_2 40 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 81 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 281 (accept_3_2 37 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 281 (Polychromatic418967fa.accept_19_17_5_15_1_7921 36 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 281 (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 281 (accept_3_2 34 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 281 (accept_3_2 31 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 281 (Polychromatic418967fa.accept_18_12_9_11_1_4370 30 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 281 (Polychromatic418967fa.accept_16_13_1_9_1_2597 29 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 281 (accept_3_2 28 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 81 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 281 (accept_3_2 25 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 281 (Polychromatic418967fa.accept_19_4_5_15_1_2437 23 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 281 (accept_3_2 22 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 281 (Polychromatic418967fa.accept_16_5_1_9_1_4621 21 81 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 281 (accept_3_2 19 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 281 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 281 (accept_3_2 16 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 281 (accept_3_2 13 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 281 (accept_3_2 10 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 281 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 81 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 281 (accept_3_2 7 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  281 (Polychromatic418967fa.accept_19_6_5_15_1_13340 6 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 81 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 281 (accept_3_2 4 81 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 281 (accept_3_2 1 81 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 281
  (allA_succ_of_accept 79 80 281 (accept_3_2 79 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 281 (accept_3_2 76 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 281 (accept_3_2 73 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 281 (Polychromatic418967fa.accept_13_6_2_8_1_1782 71 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 281 (accept_3_2 70 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 68 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 281 (accept_3_2 67 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 281 (accept_3_2 64 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 281 (accept_3_2 61 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 281 (accept_3_2 58 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 281
  (Polychromatic418967fa.accept_17_5_12_9_1_10091 56 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 281 (accept_3_2 55 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 281 (accept_3_2 52 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 281 (accept_3_2 49 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 281 (accept_3_2 46 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 281 (accept_3_2 43 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 281 (accept_3_2 40 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 281 (accept_3_2 37 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 281 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 281 (Polychromatic418967fa.accept_21_14_17_8_1_5239 35 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 281 (accept_3_2 34 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 281 (accept_3_2 31 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 281 (Polychromatic418967fa.accept_19_10_4_15_1_3720 29 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 281 (accept_3_2 28 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 281 (accept_3_2 25 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 281 (accept_3_2 22 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 281
  (Polychromatic418967fa.accept_11_9_3_6_1_797 20 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 281 (accept_3_2 19 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 281 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 281 (accept_3_2 16 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 281 (accept_3_2 13 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 281 (accept_3_2 10 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 281
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 281 (accept_3_2 7 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 80 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 80 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 281 (accept_3_2 4 80 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 80
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 281 (accept_3_2 1 80 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 281 (allA_of_3_0 79
  79 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 281 (allA_succ_of_accept 77 78 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 281 (accept_3_2 76 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 281 (Polychromatic418967fa.accept_15_14_3_11_1_850 74 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 281 (accept_3_2 73 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 281 (Polychromatic418967fa.accept_14_2_8_1_1_1647 72 78 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 281 (accept_3_2 70 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 281 (accept_3_2 67 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 281
  (Polychromatic418967fa.accept_14_9_8_1_1_2381 65 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 281 (accept_3_2 64 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 281 (accept_3_2 61 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 281 (Polychromatic418967fa.accept_11_5_1_6_1_774 60 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 281 (accept_3_2 58 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 281 (Polychromatic418967fa.accept_19_18_2_15_1_3718 56 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 281 (accept_3_2 55 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 281 (Polychromatic418967fa.accept_17_3_10_9_1_8970 54 78
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 281 (accept_3_2 52 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 281 (accept_3_2 49 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 281 (accept_3_2 46 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 281 (Polychromatic418967fa.accept_21_3_15_8_1_12962 45 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 281 (accept_3_2 43 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 281 (Polychromatic418967fa.accept_22_20_12_17_1_17232 42 78 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 281 (accept_3_2 40 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 281 (Polychromatic418967fa.accept_11_5_1_6_1_774 38 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 281 (accept_3_2 37 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 281 (accept_3_2 34 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 281 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 281 (accept_3_2 31 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 281
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 281 (accept_3_2 28 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 281 (accept_3_2 25 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 281 (Polychromatic418967fa.accept_21_3_15_8_1_12962 24 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 281 (accept_3_2 22 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 281 (Polychromatic418967fa.accept_16_4_14_9_1_4657 20 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 281 (accept_3_2 19 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 281 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 78 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 281 (accept_3_2 16 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 281 (accept_3_2 13 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 281 (accept_3_2 10 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 78 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 281 (accept_3_2 7 78 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 78 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 281 (accept_3_2 4 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 281 (Polychromatic418967fa.accept_14_2_8_1_1_1647 2 78 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 281 (accept_3_2 1 78 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  77 281 (allA_succ_of_accept 76 77 281 (accept_3_2 76 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 77 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 77 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 77 281 (Polychromatic418967fa.accept_10_4_7_1_1_471 74 77 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 281 (accept_3_2 73 77 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 281 (Polychromatic418967fa.accept_13_7_12_8_1_199
  72 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 281 (accept_3_2 70 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 68 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 281 (accept_3_2 67 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 281
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 281 (accept_3_2 64 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 281 (Polychromatic418967fa.accept_25_13_2_6_1_10427 63 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 281 (accept_3_2 61 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 281
  (Polychromatic418967fa.accept_13_7_12_8_1_199 59 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 281 (accept_3_2 58 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 281 (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 281 (accept_3_2 55 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 281 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 281 (accept_3_2 52 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 281 (Polychromatic418967fa.accept_14_8_7_1_1_1615 50 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 281 (accept_3_2 49 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 281
  (Polychromatic418967fa.accept_21_5_14_8_1_6818 47 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 281 (accept_3_2 46 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 281 (Polychromatic418967fa.accept_21_3_14_8_1_14257 45 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 281 (accept_3_2 43 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 281
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 41 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 281 (accept_3_2 40 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 281 (Polychromatic418967fa.accept_16_6_13_9_1_4690 38 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 281 (accept_3_2 37 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 77 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 281 (accept_3_2 34 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 281 (Polychromatic418967fa.accept_18_14_5_11_1_5676 32 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 281 (accept_3_2 31 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 77 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 281
  (Polychromatic418967fa.accept_22_7_11_17_1_9600 29 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 281 (accept_3_2 28 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 281 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 281 (accept_3_2 25 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 281
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 23 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 281 (accept_3_2 22 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 281 (accept_3_2 19 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 281 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 281 (accept_3_2 16 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 281 (Polychromatic418967fa.accept_10_4_7_1_1_471 14 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 281 (accept_3_2 13 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 281
  (Polychromatic418967fa.accept_19_11_1_15_1_9263 11 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 281 (accept_3_2 10 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 281 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 281 (accept_3_2 7 77 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 281
  (Polychromatic418967fa.accept_13_5_12_8_1_198 5 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 281 (accept_3_2 4 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  281 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 77 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 281 (Polychromatic418967fa.accept_19_2_1_15_1_2494 2 77 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 281 (accept_3_2 1 77 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 281 (allA_of_3_0 76 76 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 281 (allA_succ_of_accept 74 75
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 281 (accept_3_2 73 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 281 (Polychromatic418967fa.accept_13_7_10_8_1_567 72 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 281 (accept_3_2 70 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 281 (accept_3_2 67 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 281 (Polychromatic418967fa.accept_20_5_15_1_1_7278 65 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 281 (accept_3_2 64 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 281 (Polychromatic418967fa.accept_13_11_10_8_1_1804 63 75
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 281 (accept_3_2 61 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 281 (accept_3_2 58 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 281 (accept_3_2 55 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 281 (accept_3_2 52 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 281 (accept_3_2 49 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 47 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 281 (accept_3_2 46 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 281 (accept_3_2 43 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 281 (accept_3_2 40 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 281 (accept_3_2 37 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 281 (accept_3_2 34 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 281 (accept_3_2 31 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 281 (accept_3_2 28 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 281 (accept_3_2 25 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 281 (accept_3_2 22 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 281 (accept_3_2 19 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 281 (accept_3_2 16 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 281 (accept_3_2 13 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 281 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 281 (accept_3_2 10 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 75 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 281 (accept_3_2 7 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 75 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 281 (accept_3_2 4 75 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 281 (accept_3_2 1 75 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 281 (allA_succ_of_accept
  73 74 281 (accept_3_2 73 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 281
  (Polychromatic418967fa.accept_13_7_9_8_1_188 72 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 281 (accept_3_2 70 74 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 68
  74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 281 (accept_3_2 67 74
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 281 (Polychromatic418967fa.accept_7_3_4_1_1_71
  66 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 74 281
  (Polychromatic418967fa.accept_10_5_4_1_1_842 65 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 74 281 (accept_3_2 64 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  74 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 74 281 (Polychromatic418967fa.accept_19_5_17_15_1_9225 62 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 281 (accept_3_2 61 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 281 (Polychromatic418967fa.accept_19_3_17_15_1_6459 60 74
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 74 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 74 281 (accept_3_2 58 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  74 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 74 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 56 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 281 (accept_3_2 55 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 74 281
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 53 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 74 281 (accept_3_2 52 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  74 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 74 281 (Polychromatic418967fa.accept_13_11_9_8_1_1125 50 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 281 (accept_3_2 49 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 281 (Polychromatic418967fa.accept_15_3_14_11_1_1579 48 74
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 74 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 74 281 (accept_3_2 46 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  74 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 74 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 44 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 281 (accept_3_2 43 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 281 (Polychromatic418967fa.accept_13_3_9_8_1_4202 42 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 74 281
  (Polychromatic418967fa.accept_19_3_17_15_1_6459 41 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 74 281 (accept_3_2 40 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  74 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 74 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 281 (accept_3_2 37 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 281 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 74 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 74 281 (accept_3_2 34 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  74 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 74 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 32 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 281 (accept_3_2 31 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 281 (Polychromatic418967fa.accept_13_4_9_8_1_1736 30 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 74 281
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 29 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 74 281 (accept_3_2 28 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  74 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 74 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 281 (accept_3_2 25 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 74 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 74 281 (accept_3_2 22 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  74 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 74 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 281 (accept_3_2 19 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 281 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 74 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 74 281 (accept_3_2 16 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  74 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 74 281 (Polychromatic418967fa.accept_11_3_8_6_1_788 14 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 281 (accept_3_2 13 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 74 281 (accept_3_2 10 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  74 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 74 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 281 (accept_3_2 7 74 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 281 (Polychromatic418967fa.accept_20_6_14_1_1_8896 6 74 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 281 (accept_3_2 4 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 281 (Polychromatic418967fa.accept_19_2_17_15_1_1377 2 74 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 281 (accept_3_2 1 74 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  281 (allA_of_3_0 73 73 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 281 (allA_succ_of_accept 71 72 281
  (Polychromatic418967fa.accept_16_7_8_9_1_9427 71 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 281 (accept_3_2 70 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 281 (Polychromatic418967fa.accept_13_3_7_8_1_4192 68 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 281 (accept_3_2 67 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 281
  (Polychromatic418967fa.accept_16_1_8_9_1_3462 65 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 281 (accept_3_2 64 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 281 (accept_3_2 61 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 281 (Polychromatic418967fa.accept_16_12_8_9_1_2583 60 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 281 (accept_3_2 58 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 281 (Polychromatic418967fa.accept_22_13_6_17_1_17231 57 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 281 (accept_3_2 55 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 281 (Polychromatic418967fa.accept_13_2_7_8_1_4221 54 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 281
  (Polychromatic418967fa.accept_10_3_2_1_1_839 53 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 281 (accept_3_2 52 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 281 (Polychromatic418967fa.accept_13_12_7_8_1_1104 51 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 281 (Polychromatic418967fa.accept_14_8_2_1_1_1652 50 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 281 (accept_3_2 49 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 281
  (Polychromatic418967fa.accept_16_15_8_9_1_2563 47 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 281 (accept_3_2 46 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 281 (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 281 (accept_3_2 43 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 281 (Polychromatic418967fa.accept_13_3_7_8_1_4192 42 72 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 281 (accept_3_2 40 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 281 (accept_3_2 37 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 281
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 35 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 281 (accept_3_2 34 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 281 (Polychromatic418967fa.accept_22_10_6_17_1_17230 32 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 281 (accept_3_2 31 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 281 (Polychromatic418967fa.accept_17_13_4_9_1_6390 30 72
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 281
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 281 (accept_3_2 28 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 281 (accept_3_2 25 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 281
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 281 (accept_3_2 22 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 281 (Polychromatic418967fa.accept_22_21_6_17_1_14155 21 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 281 (accept_3_2 19 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 281 (Polychromatic418967fa.accept_21_18_9_8_1_11479 18 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 281 (accept_3_2 16 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 281 (Polychromatic418967fa.accept_13_2_7_8_1_4221 15 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 281 (Polychromatic418967fa.accept_13_1_7_8_1_1796 14 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 281 (accept_3_2 13 72 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 281 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 72 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 281
  (Polychromatic418967fa.accept_20_11_12_1_1_13132 11 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 72 281 (accept_3_2 10 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 72 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 281 (Polychromatic418967fa.accept_14_8_2_1_1_1652 8 72 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 281 (accept_3_2 7 72 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6
  72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 281
  (Polychromatic418967fa.accept_25_5_22_6_1_17229 5 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 281 (accept_3_2 4 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 281 (Polychromatic418967fa.accept_13_2_7_8_1_4221 2 72 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 281 (accept_3_2 1 72 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 281
  (allA_succ_of_accept 70 71 281 (accept_3_2 70 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 281 (accept_3_2 67 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 281
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 65 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 281 (accept_3_2 64 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 281 (Polychromatic418967fa.accept_13_11_6_8_1_1121 63 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 281 (accept_3_2 61 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 71 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 281 (accept_3_2 58 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 281 (Polychromatic418967fa.accept_11_1_5_6_1_397 56 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 281 (accept_3_2 55 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 281
  (Polychromatic418967fa.accept_13_1_6_8_1_208 53 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 281 (accept_3_2 52 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 281 (accept_3_2 49 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 71 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 281
  (Polychromatic418967fa.accept_20_7_11_1_1_5840 47 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 281 (accept_3_2 46 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 281 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 281 (Polychromatic418967fa.accept_17_10_3_9_1_14826 44 71 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 281 (accept_3_2 43 71 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 281 (accept_3_2 40 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 281 (accept_3_2 37 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 281 (Polychromatic418967fa.accept_19_17_14_15_1_1403 36 71 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 281
  (Polychromatic418967fa.accept_16_3_7_9_1_3474 35 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 281 (accept_3_2 34 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 281 (accept_3_2 31 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 281
  (Polychromatic418967fa.accept_16_13_7_9_1_2606 29 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 281 (accept_3_2 28 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 281 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 281 (accept_3_2 25 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 71 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 281 (accept_3_2 22 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 281 (Polychromatic418967fa.accept_18_2_17_11_1_3178 20 71 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 281 (accept_3_2 19 71 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 281
  (Polychromatic418967fa.accept_19_17_14_15_1_1403 17 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 71 281 (accept_3_2 16 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 71 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 71 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 281 (accept_3_2 13 71 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 12
  71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 281
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 281 (accept_3_2 10 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 281 (Polychromatic418967fa.accept_28_9_15_1_1_13386 9 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 281 (Polychromatic418967fa.accept_16_8_7_9_1_7052 8 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 281 (accept_3_2 7 71 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 281 (accept_3_2 4 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  281 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 71 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 281 (accept_3_2 1 71 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 281
  (allA_of_3_0 70 70 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 281 (allA_succ_of_accept 68 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 281 (accept_3_2 67 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 281 (accept_3_2 64 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 281 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 281 (accept_3_2 61 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 281 (accept_3_2 58 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 281 (accept_3_2 55 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 281 (accept_3_2 52 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 281 (accept_3_2 49 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 281 (accept_3_2 46 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 281 (accept_3_2 43 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 281 (accept_3_2 40 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 281 (accept_3_2 37 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 281 (accept_3_2 34 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 281 (accept_3_2 31 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 281 (Polychromatic418967fa.accept_16_13_5_9_1_4682 29 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 281 (accept_3_2 28 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 281 (accept_3_2 25 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 281 (Polychromatic418967fa.accept_13_11_4_8_1_1098 24 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 281 (accept_3_2 22 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 281 (accept_3_2 19 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 281 (accept_3_2 16 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 281 (accept_3_2 13 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 281 (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 281 (accept_3_2 10 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 281 (accept_3_2 7 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  281 (Polychromatic418967fa.accept_15_6_9_11_1_858 6 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 69 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 281 (accept_3_2 4 69 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 69 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 281 (accept_3_2 1 69 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 281 (allA_succ_of_accept 67 68
  281 (accept_3_2 67 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 281 (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 68 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 281 (accept_3_2 64 68 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 62
  68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 281 (accept_3_2 61 68
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 68 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 281 (accept_3_2 58 68 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 281 (Polychromatic418967fa.accept_16_8_4_9_1_4666
  56 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 281 (accept_3_2 55
  68 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 281
  (Polychromatic418967fa.accept_19_16_11_15_1_7906 54 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 281 (accept_3_2 52 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 281 (accept_3_2 49 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 281 (Polychromatic418967fa.accept_19_9_11_15_1_6406 47 68 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 281 (accept_3_2 46 68 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 281 (accept_3_2 43 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 281 (accept_3_2 40 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 281 (accept_3_2 37 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 281 (Polychromatic418967fa.accept_21_15_5_8_1_17228 36 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 281 (accept_3_2 34 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 281 (accept_3_2 31 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 281 (accept_3_2 28 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 281 (accept_3_2 25 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 281 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 281 (accept_3_2 22 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 281 (accept_3_2 19 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 281 (accept_3_2 16 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 281 (accept_3_2 13 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 281 (accept_3_2 10 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 281 (accept_3_2 7 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 68 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 281 (accept_3_2 4 68 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  68 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 281 (accept_3_2 1 68 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 281 (allA_of_3_0 67 67 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 281 (allA_succ_of_accept 65 66 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 281 (accept_3_2 64 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 281 (accept_3_2 61 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 66 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 281 (accept_3_2 58 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 281 (Polychromatic418967fa.accept_10_7_6_1_1_486 57 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 281 (Polychromatic418967fa.accept_19_18_9_15_1_14693 56 66 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 281 (accept_3_2 55 66 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 66 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 281 (accept_3_2 52 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 281 (accept_3_2 49 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 281 (Polychromatic418967fa.accept_13_9_1_8_1_1742 48 66 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 281 (accept_3_2 46 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 281 (accept_3_2 43 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 66 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 281 (accept_3_2 40 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 281 (Polychromatic418967fa.accept_13_12_1_8_1_1779 38 66 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 281 (accept_3_2 37 66 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 281 (Polychromatic418967fa.accept_20_16_6_1_1_7270 36 66
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 281 (accept_3_2 34 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 281 (accept_3_2 31 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 66 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 281
  (Polychromatic418967fa.accept_19_10_9_15_1_11965 29 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 66 281 (accept_3_2 28 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 66 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 66 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 281 (accept_3_2 25 66 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 24
  66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 281 (accept_3_2 22 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 281 (Polychromatic418967fa.accept_19_2_9_15_1_9238 21 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 281 (Polychromatic418967fa.accept_13_7_1_8_1_1778 20 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 281 (accept_3_2 19 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 66 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 281 (accept_3_2 16 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 281 (accept_3_2 13 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 66 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 281 (accept_3_2 10 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 281 (accept_3_2 7 66 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 66 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 281 (accept_3_2 4 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 66 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 281 (accept_3_2 1 66 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 281
  (allA_succ_of_accept 64 65 281 (accept_3_2 64 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 281 (Polychromatic418967fa.accept_17_12_14_9_1_5079 63 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 281 (accept_3_2 61 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 281 (Polychromatic418967fa.accept_11_5_10_6_1_793 60 65 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 281 (accept_3_2 58 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 281 (Polychromatic418967fa.accept_21_15_2_8_1_14291 57 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 281 (accept_3_2 55 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 65 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 281
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 53 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 281 (accept_3_2 52 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 281 (Polychromatic418967fa.accept_15_6_5_11_1_2378 51 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 281 (Polychromatic418967fa.accept_14_8_9_1_1_3313 50 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 281 (accept_3_2 49 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 65 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 281
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 281 (accept_3_2 46 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 44 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 281 (accept_3_2 43 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 281 (Polychromatic418967fa.accept_16_10_1_9_1_4622 42 65 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 281 (accept_3_2 40 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 281 (accept_3_2 37 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 65 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 281
  (Polychromatic418967fa.accept_19_16_8_15_1_6447 35 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 281 (accept_3_2 34 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 281 (Polychromatic418967fa.accept_26_7_13_21_1_13696 33 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 281 (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 65 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 281 (accept_3_2 31 65 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 281 (Polychromatic418967fa.accept_20_10_5_1_1_4406 30 65
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 281
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 281 (accept_3_2 28 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 281 (accept_3_2 25 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 65 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 281
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 281 (accept_3_2 22 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 281 (Polychromatic418967fa.accept_15_6_5_11_1_2378 21 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 281 (accept_3_2 19 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 281 (Polychromatic418967fa.accept_16_2_1_9_1_2577 18 65 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 281 (accept_3_2 16 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 281 (Polychromatic418967fa.accept_20_15_5_1_1_5899 15 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 281 (accept_3_2 13 65 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 281 (Polychromatic418967fa.accept_17_12_14_9_1_5079 12 65 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 281
  (Polychromatic418967fa.accept_26_11_13_21_1_17227 11 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 65 281 (accept_3_2 10 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 65 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 281 (Polychromatic418967fa.accept_14_8_9_1_1_3313 8 65 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 281 (accept_3_2 7 65 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6
  65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 281
  (Polychromatic418967fa.accept_11_5_10_6_1_793 5 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 281 (accept_3_2 4 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 65 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 281 (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 65 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 281 (accept_3_2 1 65 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 281
  (allA_of_3_0 64 64 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 281 (allA_succ_of_accept 62 63 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 281 (accept_3_2 61 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 281 (Polychromatic418967fa.accept_22_16_19_17_1_12666 60 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 281 (Polychromatic418967fa.accept_15_14_3_11_1_850 59 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 281 (accept_3_2 58 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 63 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 281 (accept_3_2 55 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 281 (Polychromatic418967fa.accept_13_1_11_8_1_2562 53 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 281 (accept_3_2 52 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 51 63 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 281 (accept_3_2 49 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 281 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 281 (Polychromatic418967fa.accept_11_3_8_6_1_788 47 63 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 281 (accept_3_2 46 63 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 281 (accept_3_2 43 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 281 (Polychromatic418967fa.accept_14_13_7_1_1_1618 41 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 281 (accept_3_2 40 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 281 (Polychromatic418967fa.accept_17_5_12_9_1_10091 39 63
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 281 (accept_3_2 37 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 281 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 281 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 63 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 281 (accept_3_2 34 63 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 281 (accept_3_2 31 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 281 (Polychromatic418967fa.accept_13_3_11_8_1_1094 29 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 281 (accept_3_2 28 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 281 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 63
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 281 (accept_3_2 25 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 281 (Polychromatic418967fa.accept_16_8_15_9_1_4676 24 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 281 (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 281 (accept_3_2 22 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 281 (accept_3_2 19 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 281 (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 281 (accept_3_2 16 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 281 (Polychromatic418967fa.accept_18_15_9_11_1_4371 15 63
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 281 (accept_3_2 13 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 281 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 281 (Polychromatic418967fa.accept_19_11_6_15_1_14622 11 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 281 (accept_3_2 10 63 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 281 (accept_3_2 7 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 281 (Polychromatic418967fa.accept_17_5_12_9_1_10091 5 63 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 281 (accept_3_2 4 63 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 281 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 63 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 281 (accept_3_2 1 63 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 281 (allA_succ_of_accept 61 62 281
  (accept_3_2 61 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 281
  (Polychromatic418967fa.accept_9_6_8_2_1_410 60 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 281 (accept_3_2 58 62 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 281 (Polychromatic418967fa.accept_10_6_2_1_1_494
  56 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 281 (accept_3_2 55
  62 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 62 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 281 (accept_3_2 52 62 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 50
  62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 281 (accept_3_2 49 62
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 281
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 281 (accept_3_2 46 62 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 44
  62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 281 (accept_3_2 43 62
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 281
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 62 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 281 (accept_3_2 40 62 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 281
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 38 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 281 (accept_3_2 37 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 281 (accept_3_2 34 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 281 (accept_3_2 31 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 281 (accept_3_2 28 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 281 (accept_3_2 25 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 281 (accept_3_2 22 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 281 (accept_3_2 19 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 281 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 281 (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 62 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 281 (accept_3_2 16 62 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 281 (accept_3_2 13 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 281 (accept_3_2 10 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 281 (accept_3_2 7 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 62 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 62 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 281 (accept_3_2 4 62 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 62
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 281 (accept_3_2 1 62 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 281 (allA_of_3_0 61 61 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 281 (allA_succ_of_accept 59 60 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 281 (accept_3_2 58 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 281 (Polychromatic418967fa.accept_11_1_5_6_1_397 56 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 281 (accept_3_2 55 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 60 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 281 (accept_3_2 52 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 281 (Polychromatic418967fa.accept_16_3_12_9_1_8250 51 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 281 (accept_3_2 49 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 60 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 281 (accept_3_2 46 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 281 (accept_3_2 43 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 281 (Polychromatic418967fa.accept_23_19_14_5_1_17226 42 60 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 281 (accept_3_2 40 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 281 (accept_3_2 37 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 281 (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 60 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 281 (accept_3_2 34 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 281 (accept_3_2 31 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 60 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 281 (accept_3_2 28 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 281 (Polychromatic418967fa.accept_19_8_3_15_1_2510 27 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 281 (accept_3_2 25 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 60 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 281 (accept_3_2 22 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 281 (Polychromatic418967fa.accept_16_4_12_9_1_2567 20 60 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 281 (accept_3_2 19 60 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 281 (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 60
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 281 (accept_3_2 16 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 281 (Polychromatic418967fa.accept_18_15_6_11_1_5651 15 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 281 (accept_3_2 13 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 60 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 281
  (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 281 (accept_3_2 10 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 281 (Polychromatic418967fa.accept_19_9_3_15_1_2429 9 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 281 (accept_3_2 7 60 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 281 (Polychromatic418967fa.accept_23_6_14_5_1_17225 6 60 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 281 (accept_3_2 4 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  281 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 281 (Polychromatic418967fa.accept_16_2_12_9_1_2568 2 60 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 281 (accept_3_2 1 60 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 281
  (allA_succ_of_accept 58 59 281 (accept_3_2 58 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 281 (Polychromatic418967fa.accept_19_18_2_15_1_3718 56 59 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 281 (accept_3_2 55 59 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 281 (accept_3_2 52 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 281 (accept_3_2 49 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 59 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 281 (accept_3_2 46 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 281 (accept_3_2 43 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 281
  (Polychromatic418967fa.accept_13_2_7_8_1_4221 41 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 281 (accept_3_2 40 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 281 (accept_3_2 37 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 281 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 59 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 281 (accept_3_2 34 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 281 (accept_3_2 31 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 281
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 29 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 281 (accept_3_2 28 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 281 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 281 (accept_3_2 25 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 281 (accept_3_2 22 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 281 (Polychromatic418967fa.accept_16_4_11_9_1_1631 20 59 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 281 (accept_3_2 19 59 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 281 (accept_3_2 16 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 281 (accept_3_2 13 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 59 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 281 (accept_3_2 10 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 281 (accept_3_2 7 59 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 281 (accept_3_2 4 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  281 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 59 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 281 (accept_3_2 1 59 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 281 (allA_of_3_0
  58 58 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 281 (allA_succ_of_accept 56 57 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 281 (accept_3_2 55 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 281 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 281 (accept_3_2 52 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 57 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 281 (accept_3_2 49 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 281 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 281 (Polychromatic418967fa.accept_21_5_15_8_1_9935 47 57 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 281 (accept_3_2 46 57 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 281 (Polychromatic418967fa.accept_21_3_15_8_1_12962 45 57
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 281 (accept_3_2 43 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 281 (accept_3_2 40 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 57 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 281 (accept_3_2 37 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 281 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 281 (accept_3_2 34 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 57 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 281 (accept_3_2 31 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 281 (Polychromatic418967fa.accept_20_10_17_1_1_8852 30 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 281 (Polychromatic418967fa.accept_13_3_5_8_1_1099 29 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 281 (accept_3_2 28 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 57 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 281 (accept_3_2 25 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 281 (accept_3_2 22 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 281 (Polychromatic418967fa.accept_22_21_13_17_1_7959 21 57 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 281 (accept_3_2 19 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 281 (Polychromatic418967fa.accept_20_18_17_1_1_10388 18 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 281 (accept_3_2 16 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 281 (accept_3_2 13 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 281 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 281 (Polychromatic418967fa.accept_20_11_17_1_1_13117 11 57 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 281 (accept_3_2 10 57 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 281 (Polychromatic418967fa.accept_25_9_7_6_1_17224 9 57 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 281 (accept_3_2 7 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 57 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 57 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 281 (accept_3_2 4 57 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 57 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 281 (accept_3_2 1 57 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 281 (allA_succ_of_accept 55 56 281 (accept_3_2 55 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 281 (Polychromatic418967fa.accept_19_16_18_15_1_3681 54 56 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 281 (Polychromatic418967fa.accept_18_17_2_11_1_9749 53 56
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 281 (accept_3_2 52 56 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 281 (accept_3_2 49 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 281 (Polychromatic418967fa.accept_13_9_4_8_1_1752 48 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 281 (Polychromatic418967fa.accept_10_7_6_1_1_486 47 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 281 (accept_3_2 46 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 281
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 44 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 281 (accept_3_2 43 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 281 (Polychromatic418967fa.accept_17_7_5_9_1_7763 41 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 281 (accept_3_2 40 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 281
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 281 (accept_3_2 37 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 281 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 281 (accept_3_2 34 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 281
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 281 (accept_3_2 31 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 281 (Polychromatic418967fa.accept_17_13_5_9_1_1762 30 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 281 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 281 (accept_3_2 28 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 281 (accept_3_2 25 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 281 (Polychromatic418967fa.accept_13_11_4_8_1_1098 24 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 281 (Polychromatic418967fa.accept_13_10_4_8_1_2570 23 56 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 281 (accept_3_2 22 56 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 281
  (Polychromatic418967fa.accept_16_4_8_9_1_4639 20 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 281 (accept_3_2 19 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 281 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 281 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 281 (accept_3_2 16 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 281 (accept_3_2 13 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 281 (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 56 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 281 (accept_3_2 10 56 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 281
  (Polychromatic418967fa.accept_27_8_2_11_1_5672 8 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 281 (accept_3_2 7 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  281 (Polychromatic418967fa.accept_20_6_16_1_1_7262 6 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 56 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 281 (accept_3_2 4 56 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 281
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 281 (accept_3_2 1 56 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 281 (allA_of_3_0 55 55 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 54 281 (allA_succ_of_accept 53 54 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 281 (accept_3_2 52 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  54 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 54 281 (Polychromatic418967fa.accept_15_5_9_11_1_4398 50 54 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 281 (accept_3_2 49 54 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 54 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 281 (accept_3_2 46 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  54 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 54 281 (Polychromatic418967fa.accept_17_10_3_9_1_14826 44 54 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 281 (accept_3_2 43 54 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 281 (Polychromatic418967fa.accept_22_20_10_17_1_9639 42 54
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 54 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 281 (accept_3_2 40 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  54 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 54 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 54 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 281 (accept_3_2 37 54 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 281 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 54 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 281 (accept_3_2 34 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  54 281 (Polychromatic418967fa.accept_13_7_2_8_1_1746 33 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 54 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 54 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 281 (accept_3_2 31 54 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 281 (Polychromatic418967fa.accept_19_11_16_15_1_11951 30 54 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 281
  (Polychromatic418967fa.accept_16_13_6_9_1_2561 29 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 281 (accept_3_2 28 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  54 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 54 281 (Polychromatic418967fa.accept_20_6_14_1_1_8896 26 54 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 281 (accept_3_2 25 54 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 54 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 281 (accept_3_2 22 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  54 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 21 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 54 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 54 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 281 (accept_3_2 19 54 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 54 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 281 (accept_3_2 16 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  54 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 54 281 (Polychromatic418967fa.accept_21_14_12_8_1_6833 14 54 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 281 (accept_3_2 13 54 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 281 (Polychromatic418967fa.accept_19_12_16_15_1_3754 12 54
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 281 (accept_3_2 10 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  54 281 (Polychromatic418967fa.accept_21_9_12_8_1_5255 9 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 54 281 (Polychromatic418967fa.accept_19_8_16_15_1_9249 8 54 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 281 (accept_3_2 7 54 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 54 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 281
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 281 (accept_3_2 4 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54
  281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 54 281 (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 54 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 281 (accept_3_2 1 54 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 54 281)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 281
  (allA_succ_of_accept 52 53 281 (accept_3_2 52 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  53 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 281 (accept_3_2 49 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 53 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 281 (accept_3_2 46 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 281 (accept_3_2 43 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 281 (accept_3_2 40 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 281 (accept_3_2 37 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 53 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 281
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 281 (accept_3_2 34 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 281 (accept_3_2 31 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 53 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 281
  (Polychromatic418967fa.accept_16_13_5_9_1_4682 29 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 281 (accept_3_2 28 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 281 (Polychromatic418967fa.accept_15_12_8_11_1_4383 27 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 281 (accept_3_2 25 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 281 (accept_3_2 22 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 281 (accept_3_2 19 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 281 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 53 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 281 (accept_3_2 16 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 281 (accept_3_2 13 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 281
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 281 (accept_3_2 10 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 281 (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 281 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 281 (accept_3_2 7 53 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 53 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 281 (accept_3_2 4 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  281 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 53 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 281 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 53 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 281 (accept_3_2 1 53 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 281))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 281 (allA_of_3_0 52 52
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 281 (allA_succ_of_accept 50 51 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 281 (accept_3_2 49 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 281 (Polychromatic418967fa.accept_15_2_6_11_1_1587 47 51 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 281 (accept_3_2 46 51 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 51 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 281 (accept_3_2 43 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 51 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 281 (accept_3_2 40 51 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 51 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 281 (accept_3_2 37 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 281 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 51 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 281 (accept_3_2 34 51 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 51 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 281 (accept_3_2 31 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 281 (Polychromatic418967fa.accept_26_3_25_21_1_11822 29 51 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 281 (accept_3_2 28 51 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 281 (accept_3_2 25 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 51 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 281 (accept_3_2 22 51 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 281 (accept_3_2 19 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 51 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 281 (accept_3_2 16 51 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 281 (Polychromatic418967fa.accept_27_15_24_11_1_17223 15 51 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 281 (accept_3_2 13 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 281 (Polychromatic418967fa.accept_22_11_7_17_1_17222 11 51 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 281 (accept_3_2 10 51 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 51 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 281 (accept_3_2 7 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 51 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 281 (accept_3_2 4 51 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 281 (accept_3_2 1 51 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 281)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 281 (allA_succ_of_accept 49 50 281 (accept_3_2 49 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 50 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 281 (accept_3_2 46 50 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 281 (accept_3_2 43 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 281 (Polychromatic418967fa.accept_18_5_14_11_1_2073 41 50 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 281 (accept_3_2 40 50 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 281
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 38 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 281 (accept_3_2 37 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 281 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 281 (accept_3_2 34 50 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 281 (accept_3_2 31 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 281 (Polychromatic418967fa.accept_13_3_11_8_1_1094 29 50 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 281 (accept_3_2 28 50 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 281 (accept_3_2 25 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 281 (accept_3_2 22 50 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 281 (accept_3_2 19 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 281 (Polychromatic418967fa.accept_19_18_12_15_1_9288 18 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 50 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 281 (accept_3_2 16 50 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 281
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 14 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 281 (accept_3_2 13 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 281 (accept_3_2 10 50 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 281 (accept_3_2 7 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  281 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 281 (Polychromatic418967fa.accept_18_5_14_11_1_2073 5 50 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 281 (accept_3_2 4 50 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 281 (Polychromatic418967fa.accept_14_2_8_1_1_1647 2
  50 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 281 (accept_3_2 1 50 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 281)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 281 (allA_of_3_0 49 49 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 281 (allA_succ_of_accept 47 48
  281 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 281 (accept_3_2 46 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 281 (Polychromatic418967fa.accept_18_9_12_11_1_5642 45 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 281 (accept_3_2 43 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 48 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 281 (accept_3_2 40 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 281 (Polychromatic418967fa.accept_13_12_9_8_1_2595 38 48 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 281 (accept_3_2 37 48 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 48 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 281 (accept_3_2 34 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 281 (accept_3_2 31 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 48 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 281
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 281 (accept_3_2 28 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 281 (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 281 (accept_3_2 25 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 48 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 281 (accept_3_2 22 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 281 (Polychromatic418967fa.accept_14_7_6_1_1_1656 21 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 281 (Polychromatic418967fa.accept_13_7_9_8_1_188 20 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 281 (accept_3_2 19 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 281 (Polychromatic418967fa.accept_20_18_8_1_1_10382 18 48 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 281 (accept_3_2 16 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 281 (accept_3_2 13 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 48 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 281
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 281 (accept_3_2 10 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 281 (accept_3_2 7 48 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 48 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 281 (accept_3_2 4 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  281 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 48 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 48 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 281 (accept_3_2 1 48 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 281)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 281 (allA_succ_of_accept 46
  47 281 (accept_3_2 46 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 281 (Polychromatic418967fa.accept_10_4_7_1_1_471 44 47 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 281 (accept_3_2 43 47 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 41
  47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 281 (accept_3_2 40 47
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 281 (accept_3_2 37 47 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 281 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 47 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 281 (Polychromatic418967fa.accept_15_5_2_11_1_1596
  35 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 281 (accept_3_2 34
  47 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 281
  (Polychromatic418967fa.accept_17_16_13_9_1_11391 33 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 47 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 281 (accept_3_2 31 47 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 281
  (Polychromatic418967fa.accept_19_10_9_15_1_11965 29 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 47 281 (accept_3_2 28 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 47 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 47 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 281 (accept_3_2 25 47 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24
  47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 281
  (Polychromatic418967fa.accept_19_4_9_15_1_6405 23 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 281 (accept_3_2 22 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 281 (Polychromatic418967fa.accept_15_6_2_11_1_325 21 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 47 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 281 (accept_3_2 19 47 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 281 (accept_3_2 16 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 281 (Polychromatic418967fa.accept_20_15_7_1_1_5885 15 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 281 (accept_3_2 13 47 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 281 (Polychromatic418967fa.accept_21_12_5_8_1_9929 12 47 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 281 (accept_3_2 10 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 281 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 281 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 47 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 281 (accept_3_2 7 47 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 281
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 281 (accept_3_2 4 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 47 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 281 (accept_3_2 1 47 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 281))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 281 (allA_of_3_0 46 46 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 281 (allA_succ_of_accept 44 45 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 281 (accept_3_2 43 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 281 (Polychromatic418967fa.accept_17_8_11_9_1_5099 42 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 281 (Polychromatic418967fa.accept_13_2_6_8_1_1092 41 45 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 281 (accept_3_2 40 45 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 45 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 281 (accept_3_2 37 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 281 (Polychromatic418967fa.accept_20_15_5_1_1_5899 35 45 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 281 (accept_3_2 34 45 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 281 (accept_3_2 31 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 45 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 281 (accept_3_2 28 45 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 281 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 45 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 281 (accept_3_2 25 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 45 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 281 (accept_3_2 22 45 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 281 (Polychromatic418967fa.accept_16_5_13_9_1_2594 21 45 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 281 (accept_3_2 19 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 281 (Polychromatic418967fa.accept_16_1_13_9_1_2551 17 45 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 281 (accept_3_2 16 45 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 45 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 281 (accept_3_2 13 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 45 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 281 (accept_3_2 10 45 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 281 (accept_3_2 7 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  281 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 45 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 45 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 281 (accept_3_2 4 45 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 45 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 281 (accept_3_2 1 45 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 281))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  281 (allA_succ_of_accept 43 44 281 (accept_3_2 43 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 44 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 281 (accept_3_2 40 44 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 281 (accept_3_2 37 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 281 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 281 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 44 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 281 (accept_3_2 34 44 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 281 (accept_3_2 31 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 44 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 281 (accept_3_2 28 44 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 281 (accept_3_2 25 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 281 (accept_3_2 22 44 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 281 (accept_3_2 19 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 281 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 44 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 281 (accept_3_2 16 44 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 281 (accept_3_2 13 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 281 (Polychromatic418967fa.accept_19_11_6_15_1_14622 11 44 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 281 (accept_3_2 10 44 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 281
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 8 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 281 (accept_3_2 7 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 44 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 281 (accept_3_2 4 44 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  44 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 281 (accept_3_2 1 44 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 281)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  281 (allA_of_3_0 43 43 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 281 (allA_succ_of_accept 41 42 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 281 (accept_3_2 40 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 281 (Polychromatic418967fa.accept_15_8_12_11_1_1570 38 42 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 281 (accept_3_2 37 42 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 281 (accept_3_2 34 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 42 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 281 (accept_3_2 31 42 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 42 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 281
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 281 (accept_3_2 28 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 42 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 281 (accept_3_2 25 42 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 42 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 281 (accept_3_2 22 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 281 (Polychromatic418967fa.accept_13_7_3_8_1_1750 20 42 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 281 (accept_3_2 19 42 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 281 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 42 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 281 (accept_3_2 16 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 42 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 281 (accept_3_2 13 42 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 42 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 281 (accept_3_2 10 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 42 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 42 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 281 (accept_3_2 7 42 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 281 (accept_3_2 4 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 281 (Polychromatic418967fa.accept_26_2_16_21_1_17221 2 42 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 281 (accept_3_2 1 42 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 281)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 281 (allA_succ_of_accept 40 41
  281 (accept_3_2 40 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 281
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 281 (Polychromatic418967fa.accept_21_17_20_8_1_9938 38 41 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 281 (accept_3_2 37 41 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 281 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 41 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 35
  41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 281 (accept_3_2 34 41
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 281 (Polychromatic418967fa.accept_13_6_2_8_1_1782 32 41 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 281 (accept_3_2 31 41 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 41 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 281
  (Polychromatic418967fa.accept_19_10_3_15_1_13355 29 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 41 281 (accept_3_2 28 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 41 281 (Polychromatic418967fa.accept_19_8_3_15_1_2510 27 41 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 41 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 281 (accept_3_2 25 41 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 24
  41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 281 (accept_3_2 22 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 281 (Polychromatic418967fa.accept_13_7_2_8_1_1746 20 41 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 281 (accept_3_2 19 41 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 281 (Polychromatic418967fa.accept_19_18_3_15_1_3765 18 41 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 281 (accept_3_2 16 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 281 (Polychromatic418967fa.accept_11_3_8_6_1_788 14 41 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 281 (accept_3_2 13 41 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 281
  (Polychromatic418967fa.accept_21_11_20_8_1_8403 11 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 281 (accept_3_2 10 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 281 (accept_3_2 7 41 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 281 (accept_3_2 4 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  281 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 41 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 41 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 281 (accept_3_2 1 41 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 281))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 281 (allA_of_3_0 40 40 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 281 (allA_succ_of_accept 38 39 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 281 (accept_3_2 37 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 39 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 281 (accept_3_2 34 39 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 39 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 281 (accept_3_2 31 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 281 (Polychromatic418967fa.accept_16_13_7_9_1_2606 29 39 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 281 (accept_3_2 28 39 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 281 (Polychromatic418967fa.accept_19_8_1_15_1_2496 27 39
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 281 (accept_3_2 25 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 39 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 281 (accept_3_2 22 39 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 39 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 281 (accept_3_2 19 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 39 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 281 (accept_3_2 16 39 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 39 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 281 (accept_3_2 13 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 281 (Polychromatic418967fa.accept_19_11_1_15_1_9263 11 39 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 281 (accept_3_2 10 39 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 39 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 281 (accept_3_2 7 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 39 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 281 (accept_3_2 4 39 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 281 (accept_3_2 1 39 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 281))))))))))))))))))))))))))))))))))))))) (allB_succ 38 281
  (allA_succ_of_accept 37 38 281 (accept_3_2 37 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 281 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 281 (accept_3_2 34 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 281 (accept_3_2 31 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 281 (accept_3_2 28 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 281 (accept_3_2 25 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 281 (Polychromatic418967fa.accept_21_3_17_8_1_8402 24 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 281 (accept_3_2 22 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 281 (accept_3_2 19 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 281 (Polychromatic418967fa.accept_13_4_12_8_1_197 17 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 281 (accept_3_2 16 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 281
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 14 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 281 (accept_3_2 13 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 281 (accept_3_2 10 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 281 (accept_3_2 7 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  281 (Polychromatic418967fa.accept_24_6_14_17_1_15668 6 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 38 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 281 (accept_3_2 4 38 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 38 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 38 281 (accept_3_2 1 38 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  281)))))))))))))))))))))))))))))))))))))) (allB_succ 37 281 (allA_of_3_0 37 37 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 36 281 (allA_succ_of_accept 35 36 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 36 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 281 (accept_3_2 34 36 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 281 (Polychromatic418967fa.accept_13_7_10_8_1_567
  33 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 281
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 281 (accept_3_2 31 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  36 281 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 36 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 36 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 281 (accept_3_2 28 36 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 281 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 36 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 281
  (Polychromatic418967fa.accept_19_7_17_15_1_6453 26 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 281 (accept_3_2 25 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  36 281 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 36 281 (Polychromatic418967fa.accept_14_9_8_1_1_2381 23 36 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 281 (accept_3_2 22 36 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 281
  (Polychromatic418967fa.accept_11_9_3_6_1_797 20 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 36 281 (accept_3_2 19 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  36 281 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 36 281 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 36 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 281 (accept_3_2 16 36 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 36 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 281
  (Polychromatic418967fa.accept_16_14_4_9_1_1646 14 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 281 (accept_3_2 13 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  36 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 36 281 (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 36 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 281 (accept_3_2 10 36 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 36 281 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 36 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 281
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 281 (accept_3_2 7 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36
  281 (Polychromatic418967fa.accept_20_6_16_1_1_7262 6 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 36 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 36 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 281 (accept_3_2 4 36 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 281 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 36 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 281
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 36 281 (accept_3_2 1 36 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  281)))))))))))))))))))))))))))))))))))) (allB_succ 35 281 (allA_succ_of_accept 34 35 281 (accept_3_2 34 35 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 33
  35 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 281 (accept_3_2 31 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 35 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 281 (accept_3_2 28 35 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 281 (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 35 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 281 (accept_3_2 25 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 35 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 281 (accept_3_2 22 35 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 35 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 281
  (Polychromatic418967fa.accept_13_7_9_8_1_188 20 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 281 (accept_3_2 19 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 281 (Polychromatic418967fa.accept_13_4_9_8_1_1736 17 35 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 281 (accept_3_2 16 35 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 35 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 281 (accept_3_2 13 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 281 (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 35 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 281 (accept_3_2 10 35 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 281
  (Polychromatic418967fa.accept_14_8_7_1_1_1615 8 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 281 (accept_3_2 7 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 35 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 281 (accept_3_2 4 35 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 35 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 281 (accept_3_2 1 35 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 281))))))))))))))))))))))))))))))))))) (allB_succ 34 281
  (allA_of_3_0 34 34 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 281 (allA_succ_of_accept 32 33 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 281 (accept_3_2 31 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 281 (Polychromatic418967fa.accept_13_3_7_8_1_4192 29 33 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 281 (accept_3_2 28 33 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 281 (accept_3_2 25 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 33 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 281 (accept_3_2 22 33 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 281 (accept_3_2 19 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 33 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 281 (accept_3_2 16 33 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 33 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 281 (accept_3_2 13 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 33 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 281 (accept_3_2 10 33 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 281 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 33 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 281 (accept_3_2 7 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 33 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 33 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 281 (accept_3_2 4 33 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 281 (accept_3_2 1 33 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 281))))))))))))))))))))))))))))))))) (allB_succ 32 281
  (allA_succ_of_accept 31 32 281 (accept_3_2 31 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  32 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 32 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 32 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 281 (accept_3_2 28 32 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 281 (accept_3_2 25 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 32 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 281 (accept_3_2 22 32 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 281
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 281 (accept_3_2 19 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 281 (Polychromatic418967fa.accept_17_1_15_9_1_1743 18 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 32 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 281 (accept_3_2 16 32 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 281 (accept_3_2 13 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 281 (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 32 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 281 (accept_3_2 10 32 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 281 (accept_3_2 7 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  281 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 32 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 32 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 281 (accept_3_2 4 32 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  32 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 281 (accept_3_2 1 32 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 281)))))))))))))))))))))))))))))))) (allB_succ 31 281
  (allA_of_3_0 31 31 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 281 (allA_succ_of_accept 29 30 281
  (Polychromatic418967fa.accept_19_10_11_15_1_3699 29 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 30 281 (accept_3_2 28 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 30 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 30 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 281 (accept_3_2 25 30 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24
  30 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 281 (accept_3_2 22 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 281 (Polychromatic418967fa.accept_16_5_14_9_1_2572 21 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 30 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 281 (accept_3_2 19 30 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 281 (Polychromatic418967fa.accept_21_18_9_8_1_11479 18 30 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 281 (accept_3_2 16 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 30 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 281 (accept_3_2 13 30 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 281 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 30 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 281 (accept_3_2 10 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 281 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 30 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 30 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 281 (accept_3_2 7 30 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 30 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 281 (accept_3_2 4 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 281 (Polychromatic418967fa.accept_19_2_11_15_1_2404 2 30 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 281 (accept_3_2 1 30 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 281)))))))))))))))))))))))))))))) (allB_succ 29 281 (allA_succ_of_accept 28 29 281
  (accept_3_2 28 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 281
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 281 (Polychromatic418967fa.accept_23_3_6_5_1_10932 26 29 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 281 (accept_3_2 25 29 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 29
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 281
  (Polychromatic418967fa.accept_11_1_7_6_1_378 23 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 281 (accept_3_2 22 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 281 (Polychromatic418967fa.accept_16_5_13_9_1_2594 21 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 29 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 281 (accept_3_2 19 29 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 29 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 281
  (Polychromatic418967fa.accept_16_1_13_9_1_2551 17 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 281 (accept_3_2 16 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 281 (Polychromatic418967fa.accept_17_14_12_9_1_2774 14 29 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 281 (accept_3_2 13 29 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 29 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 281
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 281 (accept_3_2 10 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 281 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 29 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 281 (accept_3_2 7 29 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 281 (Polychromatic418967fa.accept_16_6_13_9_1_4690 6 29 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 281
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 281 (accept_3_2 4 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  281 (Polychromatic418967fa.accept_15_3_14_11_1_1579 3 29 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 29 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 29 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 281 (accept_3_2 1 29 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 29 281))))))))))))))))))))))))))))) (allB_succ 28 281 (allA_of_3_0 28 28 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 27 281 (allA_succ_of_accept 26 27 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 281 (accept_3_2 25 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 281 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 27 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 281 (accept_3_2 22 27 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 281 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 27 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 281 (accept_3_2 19 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 281 (Polychromatic418967fa.accept_19_17_8_15_1_6448 17 27 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 281 (accept_3_2 16 27 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 281 (Polychromatic418967fa.accept_18_15_9_11_1_4371 15 27
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 281 (accept_3_2 13 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 281 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 27 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 281 (accept_3_2 10 27 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 281 (accept_3_2 7 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 27 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 281 (accept_3_2 4 27 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 281 (Polychromatic418967fa.accept_17_3_10_9_1_8970 3 27 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 281 (accept_3_2 1 27 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 281))))))))))))))))))))))))))) (allB_succ 26 281
  (allA_succ_of_accept 25 26 281 (accept_3_2 25 26 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  26 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 26 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 281 (accept_3_2 22 26 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 26 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 281 (accept_3_2 19 26 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 26 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 26 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 281 (accept_3_2 16 26 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 26 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 281 (accept_3_2 13 26 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 26 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 281 (accept_3_2 10 26 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 26 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 281 (accept_3_2 7 26 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 26 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 281 (accept_3_2 4 26 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  26 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 281 (accept_3_2 1 26 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 281)))))))))))))))))))))))))) (allB_succ 25 281 (allA_of_3_0 25
  25 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 281 (allA_succ_of_accept 23 24 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 281 (accept_3_2 22 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  24 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 24 281 (Polychromatic418967fa.accept_15_5_9_11_1_4398 20 24 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 281 (accept_3_2 19 24 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 24 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 24 281 (accept_3_2 16 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  24 281 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 24 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 24 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 281 (accept_3_2 13 24 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 24 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 281 (accept_3_2 10 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  24 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 24 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 24 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 281 (accept_3_2 7 24 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 281 (Polychromatic418967fa.accept_13_6_11_8_1_1111 6 24 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 281 (accept_3_2 4 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24
  281 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 24 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 281 (accept_3_2 1 24 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 281)))))))))))))))))))))))) (allB_succ 23 281 (allA_succ_of_accept 22 23 281 (accept_3_2 22
  23 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 281
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 23 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 23 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 281 (accept_3_2 19 23 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  23 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 281 (accept_3_2 16 23
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 281
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 23 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 281 (accept_3_2 13 23 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 281
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 23 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 281 (accept_3_2 10 23 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 281 (Polychromatic418967fa.accept_19_9_4_15_1_1415 9 23 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 281 (accept_3_2 7 23 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 281
  (Polychromatic418967fa.accept_11_5_1_6_1_774 5 23 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 281 (accept_3_2 4 23 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 23 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 281 (accept_3_2 1 23 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 281))))))))))))))))))))))) (allB_succ 22 281 (allA_of_3_0 22 22 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 281 (allA_succ_of_accept 20 21 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 281 (accept_3_2 19 21 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 281 (Polychromatic418967fa.accept_15_3_6_11_1_855
  18 21 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 21 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 281 (accept_3_2 16 21 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 281 (accept_3_2 13 21 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 281
  (Polychromatic418967fa.accept_16_11_5_9_1_1617 11 21 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 281 (accept_3_2 10 21 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 281 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 21 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 281 (accept_3_2 7 21 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 21 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 281 (accept_3_2 4 21 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  281 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 281 (accept_3_2 1 21 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 21 281))))))))))))))))))))) (allB_succ 20 281 (allA_succ_of_accept 19 20 281 (accept_3_2 19 20
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 281
  (Polychromatic418967fa.accept_17_1_3_9_1_958 18 20 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 281 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 20 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 281 (accept_3_2 16 20 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 281 (Polychromatic418967fa.accept_11_3_9_6_1_105
  14 20 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 281 (accept_3_2 13
  20 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 20 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 281 (Polychromatic418967fa.accept_16_11_4_9_1_851 11 20 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 281 (accept_3_2 10 20 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 281 (Polychromatic418967fa.accept_15_8_5_11_1_2358
  8 20 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 281 (accept_3_2 7 20
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 281
  (Polychromatic418967fa.accept_15_6_5_11_1_2378 6 20 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 20 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 281 (accept_3_2 4 20 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 20
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 281 (accept_3_2 1 20 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 281)))))))))))))))))))) (allB_succ 19 281 (allA_of_3_0 19 19 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 18 281 (allA_succ_of_accept 17 18 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 18 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 18 281 (accept_3_2 16 18 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  18 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 18 281 (Polychromatic418967fa.accept_13_1_5_8_1_207 14 18 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 281 (accept_3_2 13 18 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 18 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 18 281 (accept_3_2 10 18 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  18 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 18 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 18 281 (Polychromatic418967fa.accept_15_8_3_11_1_849 8 18 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 281 (accept_3_2 7 18 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 18 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 18 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 18 281 (accept_3_2 4 18 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18
  281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 281 (Polychromatic418967fa.accept_19_2_18_15_1_6413 2 18 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 281 (accept_3_2 1 18 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 18 281)))))))))))))))))) (allB_succ 17 281 (allA_succ_of_accept 16 17 281 (accept_3_2 16 17 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  17 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 281 (accept_3_2 13 17 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 17 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 281 (accept_3_2 10 17 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 17 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 281
  (Polychromatic418967fa.accept_16_8_1_9_1_847 8 17 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 281 (accept_3_2 7 17 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 17 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 281 (accept_3_2 4 17 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 17 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 17
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 281 (accept_3_2 1 17 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 281))))))))))))))))) (allB_succ 16 281 (allA_of_3_0 16 16 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 281 (allA_succ_of_accept 14 15 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 281 (accept_3_2 13 15 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 15 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 281 (Polychromatic418967fa.accept_22_11_15_17_1_17220 11 15 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 281 (accept_3_2 10 15 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 15 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 281 (accept_3_2 7 15 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 15 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 281 (accept_3_2 4 15 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 15 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 281 (accept_3_2 1 15 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 281))))))))))))))) (allB_succ 14 281 (allA_succ_of_accept 13 14
  281 (accept_3_2 13 14 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 281
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 14 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 281 (accept_3_2 10 14 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  14 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 281 (accept_3_2 7 14 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  14 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 281
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 14 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 281 (accept_3_2 4 14 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 281 (Polychromatic418967fa.accept_18_2_14_11_1_3139 2 14 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 281 (accept_3_2 1 14 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 281)))))))))))))) (allB_succ 13 281 (allA_of_3_0 13 13 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 281 (allA_succ_of_accept 11 12 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 281 (accept_3_2 10 12 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 9
  12 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 12 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 281 (accept_3_2 7 12 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 12 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 281 (accept_3_2 4 12 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 281 (Polychromatic418967fa.accept_16_2_12_9_1_2568
  2 12 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 281 (accept_3_2 1 12
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 281)))))))))))) (allB_succ 11 281 (allA_succ_of_accept 10 11
  281 (accept_3_2 10 11 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 281
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 11 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 281 (Polychromatic418967fa.accept_17_8_11_9_1_5099 8 11 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 281 (accept_3_2 7 11 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 5
  11 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 281 (accept_3_2 4 11 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 11
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 281 (accept_3_2 1 11 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  281))))))))))) (allB_succ 10 281 (allA_of_3_0 10 10 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 281
  (allA_succ_of_accept 8 9 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 281 (accept_3_2 7 9 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 9 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 9
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 281 (accept_3_2 4 9 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 281 (accept_3_2 1 9 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 281)))))))))
  (allB_succ 8 281 (allA_succ_of_accept 7 8 281 (accept_3_2 7 8 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 8 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 8 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 281 (accept_3_2 4 8 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 8 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 281 (accept_3_2 1 8 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 281))))))))
  (allB_succ 7 281 (allA_of_3_0 7 7 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 281 (allA_succ_of_accept 5
  6 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 6 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 281 (accept_3_2 4 6 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 6 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 281 (accept_3_2 1 6 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 281)))))) (allB_succ 5 281 (allA_succ_of_accept 4 5 281 (accept_3_2 4 5 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 5 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 281
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 5 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 281 (accept_3_2 1 5 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 281)))))
  (allB_succ 4 281 (allA_of_3_0 4 4 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 281 (allA_succ_of_accept 2
  3 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 281 (accept_3_2 1 3 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 281)))
  (allB_succ 2 281 (allA_succ_of_accept 1 2 281 (accept_3_2 1 2 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  281)) (allB_two
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


